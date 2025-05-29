#include "kklib.h"
#include "kklib/ws_queue.h"

void kk_init_fifo(kk_ws_queue_fifo_t* q, kk_context_t* ctx) {
    atomic_init(&q->tail, 0);
    atomic_init(&q->head, 0);
}

kk_ws_queue_t* kk_ws_queue_alloc(kk_ws_queue_type_e type, kk_context_t* ctx) {
    kk_ws_queue_t* result = kk_malloc(sizeof(kk_ws_queue_t), ctx);
    if (result == NULL) {
        return result;
    }
    result->type = type;
    switch (type) {
        case lifo:
            kk_assert(false); //TODO
            break;
        case fifo:
            kk_init_fifo(&result->fifo_q, ctx);
            break;

    }
    return result;
}

void kk_ws_queue_free(const kk_ws_queue_t* q, kk_context_t* ctx) {
    kk_free(q, ctx);
}

//true if successeful
//false if not
bool kk_ws_queue_put_fifo(kk_ws_queue_fifo_t* q, void* task) {
    size_t head = kk_atomic_load_acquire(&q->head);
    size_t tail = kk_atomic_load_relaxed(&q->tail);

    if (tail - head >= queue_size) { //queue_is full
        return false;
    }

    kk_atomic_store_relaxed(q->q + (tail % queue_size), (uintptr_t)task);
    kk_atomic_store_release(&q->tail, tail + 1);
    return true;
}

bool kk_ws_queue_put(kk_ws_queue_t* q, void* task) {
    switch(q->type) {
        case lifo:
            kk_assert(false);
            break;
        case fifo:
            return kk_ws_queue_put_fifo(&q->fifo_q, task);
    }
    return false;
}


void kk_ws_queue_force_put_many_fifo(kk_ws_queue_fifo_t* q, uintptr_t* tasks, size_t sz) {
    size_t head = kk_atomic_load_acquire(&q->head);
    size_t tail = kk_atomic_load_relaxed(&q->tail);

    kk_assert(head == tail);

    for (size_t i = 0; i < sz; ++i) {
        kk_atomic_store_relaxed(q->q + ((tail + i) % queue_size), tasks[i]);
    }

    kk_atomic_store_release(&q->tail, tail + sz);
}

void kk_ws_queue_put_many(kk_ws_queue_t* q, uintptr_t* tasks, size_t sz) {
    switch(q->type) {
        case lifo:
            kk_assert(false);
            break;
        case fifo:
            kk_ws_queue_force_put_many_fifo(&q->fifo_q, tasks, sz);
            break;
    }
}

void* kk_ws_queue_pop_fifo(kk_ws_queue_fifo_t* q) {
    for (;;) {
        size_t head = kk_atomic_load_acquire(&q->head); //maybe relaxed is enough
        size_t tail = kk_atomic_load_relaxed(&q->tail);
        if (tail == head) { //queue is empty
            return NULL;
        }

        uintptr_t result = kk_atomic_load_relaxed(q->q + (head % queue_size));
        if (kk_atomic_cas_strong_acq_rel(&q->head, &head, head + 1)) {
            return (void*)result;
        }
    }
}

void* kk_ws_queue_pop(kk_ws_queue_t* q) {
    switch(q->type) {
        case lifo:
            kk_assert(false);
            break;
        case fifo:
            return kk_ws_queue_pop_fifo(&q->fifo_q);
    }
    return NULL;
}

size_t kk_ws_queue_grab_fifo(kk_ws_queue_fifo_t* q, uintptr_t* out) {
    for (;;) {
        size_t head = kk_atomic_load_acquire(&q->head); //maybe relaxed is enough
        size_t tail = kk_atomic_load_acquire(&q->tail);

        size_t num_to_grab = (tail - head + 1) / 2;

        if (num_to_grab > queue_size / 2) {
            //inconsistent head and tail, retry
            continue;
        }

        if (num_to_grab == 0) {
            return 0;
        }

        for (size_t i = 0; i < num_to_grab; ++i) {
            out[i] = kk_atomic_load_relaxed(q->q + ((head + i) % queue_size));
        }

        if (kk_atomic_cas_strong_acq_rel(&q->head, &head, head + num_to_grab)) {
            return num_to_grab;
        }
    }
}

//called by stealer, or by producer if queue is full
size_t kk_ws_queue_grab(kk_ws_queue_t* q, uintptr_t* out) {
    switch(q->type) {
        case lifo:
            kk_assert(false);
            break;
        case fifo:
            return kk_ws_queue_grab_fifo(&q->fifo_q, out);
    }
    return 0;
}

size_t kk_ws_queue_steal_fifo(kk_ws_queue_fifo_t* from, kk_ws_queue_fifo_t* to, uintptr_t* out_task) {
    //to is empty
    uintptr_t out[queue_size / 2];
    size_t num_stolen = kk_ws_queue_grab_fifo(from, out);
    if (num_stolen == 0) {
        return 0;
    }
    *out_task = out[num_stolen - 1];
    kk_ws_queue_force_put_many_fifo(to, out, num_stolen - 1);
    return num_stolen;
}

size_t kk_ws_queue_steal(kk_ws_queue_t* from, kk_ws_queue_t* to, uintptr_t* out_task) {
    kk_assert(from->type == to->type);
    switch(from->type) {
        case lifo:
            kk_assert(false);
        case fifo:
            return kk_ws_queue_steal_fifo(&from->fifo_q, &to->fifo_q, out_task);
    }
    return 0;
}
