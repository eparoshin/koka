
/*---------------------------------------------------------------------------
  Copyright 2020-2021, Microsoft Research, Daan Leijen.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/
#include "kklib.h"
#include "kklib/work_stealing_thread.h"

//TODO win


#include <pthread.h>

static void pthread_join_void(pthread_t thread) {
  pthread_join(thread, NULL);
}


/*---------------------------------------------------------------------------
  Promise
---------------------------------------------------------------------------*/

typedef void (promise_cb_t)(void*);

typedef struct promise_s {
  kk_box_t        result;
  bool is_set;
  pthread_mutex_t lock;
  promise_cb_t* cb;
  void* cb_this;
  pthread_cond_t  available;
} promise_t;


static kk_promise_t kk_promise_alloc( kk_context_t* ctx );
static void         kk_promise_set( kk_promise_t pr, kk_box_t r, kk_context_t* ctx );
// static bool         kk_promise_available( kk_promise_t pr, kk_context_t* ctx );



/*---------------------------------------------------------------------------
  cpu-bound task
---------------------------------------------------------------------------*/

typedef struct kk_task_naitive_s {
  kk_function_t     fun;
  kk_promise_t      promise;
  kk_atomic(size_t)  executed;
} kk_task_native_t;


typedef void (task_cb_t)(void*);

typedef struct kk_task_internal_s {
    void* cb_this;
    task_cb_t* cb;
} kk_task_internal_t;

enum task_type {
   native_task,
   internal_task
};

typedef struct kk_task_s {
  enum task_type tt;
  struct kk_task_s* next;
  union {
      kk_task_native_t nt;
      kk_task_internal_t it;
  };

} kk_task_t;

static void kk_task_free( kk_task_t* task, kk_context_t* ctx ) {
    switch (task->tt) {
        case native_task:
            kk_function_drop(task->nt.fun,ctx);
            kk_box_drop(task->nt.promise,ctx);
            break;
        case internal_task:
            break;
    }
    kk_free(task,ctx);
}

static kk_task_t* kk_internal_task_alloc( void* cb_this, task_cb_t* cb, kk_context_t* ctx) {
  kk_task_t* task = (kk_task_t*)kk_zalloc(kk_ssizeof(kk_task_t), ctx);
  task->tt = internal_task;
  if (task == NULL) {
      return NULL;
  }
  task->next = NULL;
  task->it.cb_this = cb_this;
  task->it.cb = cb;
  return task;
}

static kk_task_t* kk_task_alloc( kk_function_t fun, kk_promise_t p, kk_context_t* ctx ) {
  kk_task_t* task = (kk_task_t*)kk_zalloc(kk_ssizeof(kk_task_t), ctx);
  if (task == NULL) {
    kk_function_drop(fun,ctx);
    kk_box_drop(p,ctx);
    return NULL;
  }
  task->tt = native_task;
  task->nt.promise = p;
  task->nt.fun  = fun;
  task->next = NULL;
  return task;
}

static void kk_native_task_exec( kk_task_native_t* task, kk_context_t* ctx ) {
  if (!kk_function_is_null(task->fun,ctx)) {
    kk_function_dup(task->fun,ctx);
    kk_box_t res = kk_function_call(kk_box_t,(kk_function_t,kk_context_t*),task->fun,(task->fun,ctx),ctx);
    kk_box_dup(task->promise,ctx);
    kk_promise_set( task->promise, res, ctx );
  }
}

static void kk_internal_task_exec( kk_task_internal_t* task, kk_context_t* ctx ) {
    kk_assert(task->cb_this && task->cb);
    task->cb(task->cb_this);
}

static void kk_task_exec( kk_task_t* task, kk_context_t* ctx ) {
  switch(task->tt) {
      case native_task:
          kk_native_task_exec(&task->nt, ctx);
          break;
      case internal_task:
          kk_internal_task_exec(&task->it, ctx);
          break;
  }
  kk_task_free(task,ctx);
}


/*---------------------------------------------------------------------------
  task group (thread pool with task queue)
---------------------------------------------------------------------------*/

// TODO(eparoshin) windows

#include <linux/futex.h>
#include <sys/syscall.h>
#include <unistd.h>

typedef struct parking_slot_s {
    struct parking_slot_s* next;
    struct parking_slot_s* prev;
    kk_atomic(uint) epoch;
} parking_slot_t;

static_assert(sizeof(unsigned int) == 4, "");

void futex_wait(uint32_t* value, uint32_t expected_value) {
    syscall(SYS_futex, value, FUTEX_WAIT_PRIVATE, expected_value, nullptr, nullptr, 0);
}

// Wakeup 'count' threads sleeping on address of value (-1 wakes all)
void futex_wake(uint32_t* value, uint32_t count) {
    syscall(SYS_futex, value, FUTEX_WAKE_PRIVATE, count, nullptr, nullptr, 0);
}

uint32_t prepare_park(parking_slot_t* slot) {
    return kk_atomic_load_seq_cst(&slot->epoch); //zero promise bit
}

void try_park(parking_slot_t* slot, uint32_t desired) {
    futex_wait((uint32_t*)&slot->epoch, desired); //can not park if promise bit set to one
}

void wake(parking_slot_t* slot) {
    kk_atomic_add_seq_cst(&slot->epoch, 2); //dont touch promise bit
    futex_wake((uint32_t*)&slot->epoch, -1);
}


//TODO macros
void set_promise_bit_ps(parking_slot_t* ps, bool bit) {
    if (bit) {
        atomic_fetch_or(&ps->epoch, 0x1);
    } else {
        atomic_fetch_and(&ps->epoch, ~0x1);
    }
}


// SPMC ring buffer
typedef struct kk_local_queue_s {
    parking_slot_t ps;
    kk_ssize_t    gqueue_counter;
    kk_ws_queue_t* lq;
    struct kk_task_group_s* tg;
} kk_local_queue_t;

void set_promise_bit(kk_local_queue_t* lq, bool bit) {
    set_promise_bit_ps(&lq->ps, bit);
}

typedef struct kk_local_worker_s {
    kk_local_queue_t lq;
    pthread_t thread;
} kk_local_worker_t;

typedef struct kk_task_group_s {
  kk_atomic(bool) done;
  kk_task_t*      tasks;
  kk_task_t*      tasks_tail;
  size_t          num_tasks;
  pthread_mutex_t tasks_lock;
  kk_atomic(size_t) active_workers;
  pthread_cond_t  workers_finished;
  kk_atomic(size_t) state;
  pthread_mutex_t idle_lock;
  parking_slot_t idle_head;
  kk_local_worker_t* workers;
  size_t workers_count;
} kk_task_group_t;

enum constants {
    dvyukov_const = 61,
    num_lifo_pushes = 5,
};

typedef enum push_strategy {
    push_lifo,
    push_global,
    uptoyou,
} push_strategy_e;

static void incr_idle(kk_task_group_t* tg) {
    kk_atomic_add_seq_cst(&tg->state, 1ull << 32);
}

static void decr_idle(kk_task_group_t* tg) {
    kk_atomic_sub_seq_cst(&tg->state, 1ull << 32);
}

static void unlink_node(parking_slot_t* ps) {
    kk_assert(ps->next != NULL && ps->prev != NULL);
    ps->next->prev = ps->prev;
    ps->prev->next = ps->next;
    ps->next = NULL;
    ps->prev = NULL;
}

static bool wake_worker(kk_task_group_t* tg) {
    pthread_mutex_lock(&tg->idle_lock);
    if (tg->idle_head.next != &tg->idle_head) { //non empty
        parking_slot_t* worker = tg->idle_head.next;
        unlink_node(worker);
        wake(worker);
        decr_idle(tg);
        pthread_mutex_unlock(&tg->idle_lock);
        return true;
    }
    pthread_mutex_unlock(&tg->idle_lock);
    return false;
}

/*
static bool wake_worker_locked(kk_task_group_t* tg) {
    if (tg->idle_head.next != &tg->idle_head) { //non empty
        parking_slot_t* worker = tg->idle_head.next;
        tg->idle_head.next = tg->idle_head.next->next;
        wake(worker);
        decr_idle(tg);
        return true;
    }
    return false;
}

static void wake_all(kk_task_group_t* tg) {
    pthread_mutex_lock(&tg->idle_lock);
    while (wake_worker_locked(tg)) {}
    pthread_mutex_unlock(&tg->idle_lock);
}

*/
static bool wake_the_worker(kk_local_queue_t* lq) {
    kk_task_group_t* tg = lq->tg;
    parking_slot_t* ps = &lq->ps;
    pthread_mutex_lock(&tg->idle_lock);
    if (ps->next != NULL && ps->prev != NULL) {
        unlink_node(ps);
        wake(ps);
        decr_idle(tg);
        pthread_mutex_unlock(&tg->idle_lock);
        return true;
    }
    pthread_mutex_unlock(&tg->idle_lock);
    return false;
}

static void become_inactive(kk_task_group_t* tg, parking_slot_t* ps) {
    pthread_mutex_lock(&tg->idle_lock);
    kk_assert(ps->next == NULL && ps->prev == NULL);
    ps->prev = tg->idle_head.prev;
    ps->prev->next = ps;
    ps->next = &tg->idle_head;
    tg->idle_head.prev = ps;
    incr_idle(tg);
    pthread_mutex_unlock(&tg->idle_lock);
}


static void become_active(kk_task_group_t* tg, parking_slot_t* ps) {
    pthread_mutex_lock(&tg->idle_lock);
    if (ps->next == NULL && ps->prev == NULL) {
        pthread_mutex_unlock(&tg->idle_lock);
        return;
    }
    unlink_node(ps);
    decr_idle(tg);
    pthread_mutex_unlock(&tg->idle_lock);
}

static int kk_local_queue_init(kk_task_group_t* tg, kk_local_queue_t* lq, kk_context_t* ctx) {
    lq->tg = tg;
    if ((lq->lq = kk_ws_queue_alloc(fifo, ctx)) == 0) {
        return -1;
    }
    return 0;
}

static void kk_local_queue_free(kk_local_queue_t* lq, kk_context_t* ctx) {
    kk_ws_queue_free(lq->lq, ctx);
}

static void kk_enqueue_n_global(kk_task_group_t* tg, kk_task_t* thead, kk_task_t* ttail, size_t num_tasks, kk_context_t* ctx) {
    ttail->next = NULL;
    pthread_mutex_lock(&tg->tasks_lock);
    if (tg->tasks_tail == NULL) {
        tg->tasks = thead;
        tg->tasks_tail = ttail;
        tg->num_tasks = num_tasks;
        ttail->next = NULL;
        pthread_mutex_unlock(&tg->tasks_lock);
        return;
    }

    tg->tasks_tail->next = thead;
    tg->tasks_tail = ttail;
    tg->num_tasks += num_tasks;
    pthread_mutex_unlock(&tg->tasks_lock);

}

static void kk_enqueue_global(kk_task_group_t* tg, kk_task_t* task, kk_context_t* ctx) {
    kk_enqueue_n_global(tg, task, task, 1, ctx);
}

static void kk_notify_push( kk_task_group_t* tg, kk_context_t* ctx) {
    (void)ctx;
    size_t state = kk_atomic_load_seq_cst(&tg->state);
    size_t num_idle = state >> 32;
    size_t num_spinning = (state << 32) >> 32;
    if (num_idle > 0 && num_spinning == 0) {
        wake_worker(tg);
    }
}

static bool kk_try_push( kk_local_queue_t* q,  kk_task_t* task, bool islifo, kk_context_t* ctx) {
    (void)islifo; //todo
    return kk_ws_queue_put(q->lq, task);
}

static kk_task_t* pop_global_locked( kk_task_group_t* tg, kk_context_t* ctx) {
    if (tg->num_tasks == 0) {
        return nullptr;
    }

    --tg->num_tasks;
    kk_task_t* task = tg->tasks;
    tg->tasks = tg->tasks->next;
    if (tg->num_tasks == 0) {
        tg->tasks_tail = NULL;
    }
    return task;
}


static kk_task_t* kk_try_grab_global( kk_task_group_t* tg, kk_local_queue_t* q, kk_context_t* ctx) {
    pthread_mutex_lock(&tg->tasks_lock);
    size_t num_to_grab = tg->workers_count <= 1 ? tg->num_tasks : (tg->num_tasks + tg->workers_count / 2 - 1) / (tg->workers_count / 2);
    kk_task_t* tasks[queue_size];
    if (queue_size < num_to_grab) {
        num_to_grab = queue_size;
    }
    size_t grabbed = num_to_grab;
    for (size_t i = 0; i < num_to_grab; ++i) {
        kk_task_t* task = pop_global_locked( tg, ctx );
        if (task == NULL) {
            grabbed = i;
            break;
        }
        tasks[i] = task;
    }
    pthread_mutex_unlock(&tg->tasks_lock);
    if (grabbed == 0) {
        return NULL;
    }
    kk_task_t* task = tasks[grabbed - 1];
    --grabbed;
    kk_ws_queue_put_many(q->lq, (uintptr_t*)tasks, grabbed);

    return task;
}

static kk_task_t* kk_try_pop_local( kk_task_group_t* tg, kk_local_queue_t* q, kk_context_t* ctx) {
    return (kk_task_t*)kk_ws_queue_pop(q->lq);
}

static kk_task_t* kk_try_pop_global( kk_task_group_t* tg, kk_context_t* ctx) {
    pthread_mutex_lock(&tg->tasks_lock);
    kk_task_t* task = pop_global_locked( tg, ctx );
    pthread_mutex_unlock(&tg->tasks_lock);
    return task;
}

static kk_task_t* try_steal_tasks(kk_task_group_t* tg, kk_local_queue_t* lq, size_t num_tries, kk_context_t* ctx) {
    kk_task_t* task = NULL;
    for (size_t i = 0; i < num_tries; ++i) {
        size_t idx = kk_srandom_uint64(ctx) % tg->workers_count;
        for (size_t j = 0; j < tg->workers_count; ++j) {
            kk_local_queue_t* sq = &tg->workers[(j + idx) % tg->workers_count].lq;
            kk_assert(sq);
            kk_assert(lq);
            kk_assert(ctx->local_queue);
            //dont steal from myself
            if (sq == lq) {
                continue;
            }

            kk_assert(sq->lq);
            kk_assert(lq->lq);
            size_t num_stolen = kk_ws_queue_steal(sq->lq, lq->lq, (uintptr_t*)&task);
            if (num_stolen > 0) {
                return task;
            }
        }
    }
    return task;
}

static kk_task_t* kk_try_pop_before_park( kk_task_group_t* tg, kk_local_queue_t* lq, kk_context_t* ctx) {
    kk_task_t* task = NULL;
    if ((task = kk_try_pop_global(tg, ctx))) {
        return task;
    }
    if ((task = try_steal_tasks(tg, lq, 1, ctx))) {
        return task;
    }
    return task;
}


static bool try_start_spinning(kk_task_group_t* tg) {
    while (true) {
        size_t state = kk_atomic_load_seq_cst(&tg->state);
        size_t num_spinning = (state << 32) >> 32;
        //do not allow more then 1/2 workers to spin
        if (num_spinning + 1 > tg->workers_count / 2) {
            return false;
        }

        size_t new_state = state + 1;

        if (kk_atomic_cas_weak_seq_cst(&tg->state, &state, new_state)) {
            return true;
        }
    }
}

//returns
//was this worker last spinner?
static bool stop_spinning(kk_task_group_t* tg) {
    size_t prev_state = kk_atomic_dec_seq_cst(&tg->state);
    size_t num_spinning = (prev_state << 32) >> 32;
    return num_spinning == 1;
}

static kk_task_t* kk_try_pop( kk_task_group_t* tg, kk_local_queue_t* lq, kk_context_t* ctx) {

    //sometimes we need to pop from global queue for load balancing
    kk_task_t* task = NULL;
    if (lq->gqueue_counter % dvyukov_const == 0) {
        if ((task = kk_try_pop_global(tg, ctx))) {
            return task;
        }
    }

    if ((task = kk_try_pop_local(tg, lq, ctx))) {
        return task;
    }

    if ((task = kk_try_grab_global(tg, lq, ctx))) {
        return task;
    }

    if (try_start_spinning(tg)) {
        task = try_steal_tasks(tg, lq, 4, ctx);
        bool last = stop_spinning(tg);
        if (task && last) {
            //found task
            //last spinner must wake new worker
            wake_worker(tg);
        }
        return task;
    }

    return nullptr;
}

static kk_task_t* kk_pop ( kk_task_group_t* tg, kk_local_queue_t* lq, kk_context_t* ctx) {
    while (!kk_atomic_load_relaxed(&tg->done)) {
        kk_task_t* task = NULL;
        if ((task = kk_try_pop(tg, lq, ctx))) {
            return task;
        }

        uint32_t epoch = prepare_park(&lq->ps);

        become_inactive(tg, &lq->ps);

        if ((task = kk_try_pop_before_park(tg, lq, ctx))) {
            become_active(tg, &lq->ps);
            return task;
        }

        if (kk_atomic_load_relaxed(&tg->done)) {
            become_active(tg, &lq->ps);
            return nullptr;
        }

        if (epoch & 0x1) { //promise was set
            become_active(tg, &lq->ps);
            return nullptr;
        }
        try_park(&lq->ps, epoch);
        become_active(tg, &lq->ps);

    }

    return nullptr;
}

static void kk_enqueue_local( kk_task_group_t* tg, kk_task_t* task, bool islifo, kk_context_t* ctx) {
    kk_local_queue_t* lq = ctx->local_queue;

    if (!kk_try_push(lq, task, islifo, ctx)) {
        //try push failed
        //offload 1/2 tasks to global queue
        kk_task_t* tasks_buff[queue_size / 2];
        size_t num_grabbed = kk_ws_queue_grab(lq->lq, (uintptr_t*)tasks_buff);
        kk_task_t* thead = task;
        kk_task_t* ttail = task;
        for (size_t i = 0; i < num_grabbed; ++i) {
            ttail->next = tasks_buff[i];
            ttail = tasks_buff[i];
        }
        kk_enqueue_n_global(tg, thead, ttail, num_grabbed, ctx);
    }
}


static void kk_task_group_schedule( kk_task_group_t* tg, kk_task_t* task, enum push_strategy strategy, kk_context_t* ctx ) {
  //external schedule
  if (ctx->local_queue == NULL) {
      strategy = push_global;
  }
  switch (strategy) {
      case push_lifo:
      case uptoyou:
          kk_enqueue_local(tg, task, strategy == push_lifo, ctx);
          break;
      case push_global:
          kk_enqueue_global(tg, task, ctx);
          break;
  }

  kk_notify_push(tg, ctx);
}

struct kk_worker_args_s {
    kk_task_group_t* tg;
    size_t idx;
};


static pthread_mutex_t worker_init_m;
static pthread_cond_t worker_init_c;
static size_t init_workers;

static void* kk_task_group_worker( void* vargs ) {
  struct kk_worker_args_s* args = (struct kk_worker_args_s*)vargs;
  kk_task_group_t* tg = args->tg;
  kk_context_t*    ctx = kk_get_context();
  ctx->task_group = tg;
  kk_local_queue_t* lq = &tg->workers[args->idx].lq;
  ctx->local_queue = lq;
  kk_atomic_inc_seq_cst(&tg->active_workers);
  pthread_mutex_lock(&worker_init_m);
  ++init_workers;
  pthread_mutex_unlock(&worker_init_m);
  pthread_cond_broadcast(&worker_init_c);
  while(true) {
     // deqeue task
     kk_task_t* task = NULL;
     ++lq->gqueue_counter;
     task = kk_pop(tg, lq, ctx);
     if (task == NULL) {  // due to tg->done
       break;
     }
     kk_task_exec(task,ctx);
     // todo: ensure context is cleared again?
  }
  ctx->task_group = NULL;
  kk_free(vargs, ctx);
  kk_free_context();
  size_t prev = kk_atomic_dec_seq_cst(&tg->active_workers);
  return NULL;
}


void kk_task_group_free( kk_task_group_t* tg, kk_context_t* ctx ) {
  return;
  if (tg==NULL) return;
  kk_task_t* task = NULL;
  kk_atomic_store_release(&tg->done, true);
  pthread_mutex_lock(&tg->tasks_lock);
  task = tg->tasks;
  tg->tasks = NULL;
  tg->tasks_tail = NULL;
  pthread_mutex_unlock(&tg->tasks_lock);
  // free tasks
  while( task != NULL ) {
    kk_task_t* next = task->next;
    kk_task_free(task,ctx);
    task = next;
  }

  while (wake_worker(tg)) {}
  for( kk_ssize_t i = 0; i < tg->workers_count; i++) {
    if (tg->workers[i].thread != 0) {
      pthread_join_void(tg->workers[i].thread);
    }
  }
  pthread_cond_destroy(&tg->workers_finished);
  pthread_mutex_destroy(&tg->tasks_lock);
  pthread_mutex_destroy(&tg->idle_lock);
  kk_free(tg->workers,ctx);
  kk_free(tg,ctx);
}

static _Atomic(kk_ssize_t) default_concurrency;  // = 0

void kk_task_set_default_concurrency(kk_ssize_t thread_cnt, kk_context_t* ctx) {
  const kk_ssize_t cpu_count = kk_cpu_count(ctx);
  if (thread_cnt < 0) { thread_cnt = 0; }
  else if (thread_cnt > 8*cpu_count) { thread_cnt = 8*cpu_count; };
  kk_atomic_store_release(&default_concurrency, thread_cnt);
}

static kk_task_group_t* kk_task_group_alloc( kk_ssize_t thread_cnt, kk_context_t* ctx ) {
  if (thread_cnt <= 0) {
    thread_cnt = kk_atomic_load_acquire(&default_concurrency);
  }
  const kk_ssize_t cpu_count = kk_cpu_count(ctx);
  if (thread_cnt <= 0) { thread_cnt = cpu_count + (cpu_count > 16 ? cpu_count/4 : cpu_count/2); }
  if (thread_cnt > 8*cpu_count) { thread_cnt = 8*cpu_count; };  
  kk_task_group_t* tg = (kk_task_group_t*)kk_zalloc( kk_ssizeof(kk_task_group_t), ctx );
  if (tg==NULL) return NULL;
  tg->workers = (kk_local_worker_t*)kk_zalloc( (thread_cnt+1) * sizeof(kk_local_worker_t), ctx );
  if (tg->workers == NULL) goto err;
  tg->workers_count = thread_cnt;
  tg->tasks = NULL;
  tg->tasks_tail = NULL;
  tg->idle_head.next = &tg->idle_head;
  tg->idle_head.prev = &tg->idle_head;
  if (pthread_cond_init(&worker_init_c, NULL) != 0) goto err;
  if (pthread_mutex_init(&worker_init_m, NULL) != 0) goto err;
  init_workers = 0;
  if (pthread_cond_init(&tg->workers_finished, NULL) != 0) goto err;
  if (pthread_mutex_init(&tg->tasks_lock, NULL) != 0) goto err;
  if (pthread_mutex_init(&tg->idle_lock, NULL) != 0) goto err;
  for (kk_ssize_t i = 0; i < tg->workers_count; i++) {
    if (kk_local_queue_init(tg, &tg->workers[i].lq, ctx) != 0) goto err;
  }
  for (kk_ssize_t i = 0; i < tg->workers_count; i++) {
    struct kk_worker_args_s* args = (struct kk_worker_args_s*)kk_malloc(sizeof(struct kk_worker_args_s), ctx);
    args->tg = tg;
    args->idx = i;
    if (pthread_create(&tg->workers[i].thread, NULL, &kk_task_group_worker, args) != 0) {
      goto err_threads;
    };
  }
  while (true) {
      pthread_mutex_lock(&worker_init_m);
      size_t cur_val = init_workers;
      if (cur_val == tg->workers_count) {
          pthread_mutex_unlock(&worker_init_m);
          break;
      }
      pthread_cond_wait(&worker_init_c, &worker_init_m);
      pthread_mutex_unlock(&worker_init_m);
  }
  return tg;

err_threads:
  tg->done = true;
  
err:
  if (tg != NULL) {
    if (tg->workers != NULL) { kk_free(tg->workers,ctx); }
    kk_free(tg,ctx); 
  }
  return NULL;
}

static pthread_once_t task_group_once = PTHREAD_ONCE_INIT;
static kk_task_group_t* task_group = NULL;

static void kk_task_group_init(void) {
  task_group = kk_task_group_alloc(1,kk_get_context());
}

kk_promise_t kk_task_schedule( kk_function_t fun, kk_context_t* ctx ) {
  pthread_once( &task_group_once, &kk_task_group_init ); // TODO(eparoshin) why not eager init?
                                                         // overhead for checking on every schedule
  kk_assert(task_group != NULL);
  kk_block_mark_shared( kk_datatype_as_ptr(fun,ctx), ctx);  // mark everything reachable from the task as shared
  kk_task_group_t* tg = task_group;
  kk_promise_t p = kk_promise_alloc(ctx);
  kk_task_t* task = kk_task_alloc(fun, kk_box_dup(p,ctx), ctx);

  kk_task_group_schedule( tg, task, uptoyou, ctx );
  return p;
}



/*---------------------------------------------------------------------------
  blocking promise
---------------------------------------------------------------------------*/

static void kk_promise_free( void* vp, kk_block_t* b, kk_context_t* ctx ) {
  kk_unused(b);
  promise_t* p = (promise_t*)(vp);
  pthread_cond_destroy(&p->available);
  pthread_mutex_destroy(&p->lock);  
  kk_box_drop(p->result,ctx);
  kk_free(p,ctx);
}

static kk_promise_t kk_promise_alloc(kk_context_t* ctx) {
  kk_promise_t pr;
  promise_t* p = (promise_t*)kk_zalloc(kk_ssizeof(promise_t),ctx);
  if (p == NULL) goto err;
  p->result = kk_box_any(ctx);
  if (pthread_mutex_init(&p->lock, NULL) != 0) goto err;
  if (pthread_cond_init(&p->available, NULL) != 0) goto err;
  pr = kk_cptr_raw_box( &kk_promise_free, p, ctx );
  kk_box_mark_shared(pr,ctx);
  return pr;
err:
  kk_free(p,ctx);
  return kk_box_any(ctx);
}


static void kk_promise_set( kk_promise_t pr, kk_box_t r, kk_context_t* ctx ) {
  promise_t* p = (promise_t*)kk_cptr_raw_unbox_borrowed(pr, ctx);
  kk_box_mark_shared(r,ctx);
  pthread_mutex_lock(&p->lock);
  //kk_box_drop(p->result,ctx);
  p->result = r;
  if (p->cb) {
    *(kk_box_t*)p->cb_this = kk_box_dup(p->result, ctx); //invariant - cb_this always starts with kk_box_t
    kk_task_t* task = kk_internal_task_alloc(p->cb_this, p->cb, ctx);
    kk_task_group_schedule(task_group, task, push_lifo, ctx);
  }
  pthread_mutex_unlock(&p->lock);
  pthread_cond_broadcast(&p->available);
  //kk_box_drop(pr,ctx);
}

static void promise_set_cb( kk_promise_t pr, void* cb_this, promise_cb_t* cb, kk_context_t* ctx) {
  promise_t* p = (promise_t*)kk_cptr_raw_unbox_borrowed(pr, ctx);
  pthread_mutex_lock(&p->lock);
  if (kk_box_is_any(p->result)) { //no result yet
    p->cb_this = cb_this;
    p->cb = cb;
  } else {
    *(kk_box_t*)cb_this = kk_box_dup(p->result, ctx); //invariant - cb_this always starts with kk_box_t
    kk_task_t* task = kk_internal_task_alloc(cb_this, cb, ctx);
    kk_task_group_schedule(task_group, task, push_lifo, ctx);
  }
  pthread_mutex_unlock(&p->lock);
}

/*
static bool kk_promise_available( kk_promise_t pr, kk_context_t* ctx ) {
  promise_t* p = (promise_t*)kk_cptr_raw_unbox(pr);
  pthread_mutex_lock(&p->lock);
  bool available = !kk_box_is_any(p->result);
  pthread_mutex_unlock(&p->lock);
  kk_box_drop(pr,ctx);
  return available;
}
*/

kk_promise_t kk_promise_wait_all(kk_datatype_t lst, kk_context_t* ctx) {
}

typedef struct transform_cb_s {
  kk_box_t result;
  kk_function_t fun;
  kk_promise_t p;
} transform_cb_t;

static void transform_cb(void* vthis) {
    transform_cb_t* this = (transform_cb_t*)vthis;
    kk_context_t*    ctx = kk_get_context();
    kk_box_t res = kk_function_call(kk_box_t,(kk_function_t,kk_box_t,kk_context_t*),this->fun,(this->fun,this->result,ctx),ctx);
    kk_promise_set( this->p, res, ctx);
    //kk_free(this, ctx);
}

kk_promise_t kk_promise_transform (kk_promise_t pr, kk_function_t fun, kk_context_t* ctx) {
    kk_promise_t p = kk_promise_alloc(ctx);
    transform_cb_t* cb_this = kk_zalloc(sizeof(transform_cb_t), ctx);
    cb_this->fun = fun;
    cb_this->p = kk_box_dup(p, ctx); //TODO maybe no dup
    promise_set_cb(pr, cb_this, &transform_cb, ctx);
    return p;
}

typedef struct join_cb_s {
    kk_box_t result;
    kk_promise_t p;
} join_cb_t;

static void join_cb_inner(void* vthis) {
    join_cb_t* this = (join_cb_t*)vthis;
    kk_context_t*    ctx = kk_get_context();
    kk_promise_set(this->p, this->result, ctx);
    //kk_free(this, ctx);
}

static void join_cb(void* vthis) {
    join_cb_t* this = (join_cb_t*)vthis;
    //todo unbox promise
    //tried it, looks like it works
    kk_assert(!kk_box_is_any(this->result));
    kk_promise_t inner_promise = this->result;
    kk_context_t*    ctx = kk_get_context();
    promise_set_cb(inner_promise, this, &join_cb_inner, ctx);
}

kk_promise_t kk_promise_join(kk_promise_t pr, kk_context_t* ctx) {
    kk_promise_t p = kk_promise_alloc(ctx);
    join_cb_t* cb_this = kk_zalloc(sizeof(join_cb_t), ctx);
    cb_this->p = kk_box_dup(p, ctx);
    promise_set_cb(pr, cb_this, &join_cb, ctx);
    return p;
}


kk_box_t kk_promise_get( kk_promise_t pr, kk_context_t* ctx ) {  
  promise_t* p = (promise_t*)kk_cptr_raw_unbox_borrowed(pr,ctx);
    pthread_mutex_lock( &p->lock);
    while (kk_box_is_any(p->result)) {
        pthread_cond_wait( &p->available, &p->lock );
        pthread_mutex_unlock(&p->lock);
    }
  const kk_box_t result = kk_box_dup( p->result,ctx );
  //kk_box_drop(pr,ctx);
  return result;
}
