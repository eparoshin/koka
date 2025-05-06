#include "kklib.h"
#include "kklib/ws_queue.h"


kk_ws_queue_t* kk_ws_queue_alloc(kk_context_t* ctx) {
    kk_ws_queue_t* result = kk_malloc(sizeof(kk_ws_queue_t), ctx);
    atomic_init(&result->head, 0);
    atomic_init(&result->tail, 0);
    return result;
}

void kk_ws_queue_free(const kk_ws_queue_t* q, kk_context_t* ctx) {
    kk_free(q, ctx);
}

//true if successeful
//false if not
bool kk_ws_queue_put(kk_ws_queue_t* q, void* task) {
    size_t head = kk_atomic_load_acquire(&q->head);
    size_t tail = kk_atomic_load_relaxed(&q->tail);

    if (tail - head >= queue_size) { //queue_is full
        return false;
    }

    kk_atomic_store_relaxed(q->q + (tail % queue_size), (uintptr_t)task);
    kk_atomic_store_release(&q->tail, tail + 1);
    return true;
}

void* kk_ws_queue_pop(kk_ws_queue_t* q) {
    for (;;) {
        size_t head = kk_atomic_load_acquire(&q->head);
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

size_t kk_ws_queue_steal(kk_ws_queue_t* q, kk_atomic(uintptr_t)* out_buf, size_t* out_buf_head) {
    size_t out_head = *out_buf_head;
    for (;;) {
        size_t head = kk_atomic_load_acquire(&q->head);
        size_t tail = kk_atomic_load_acquire(&q->tail);

        size_t num_to_grab = (tail - head + 1) / 2;

        for (size_t i = 0; i < num_to_grab; ++i) {
            out_buf[(out_head + i) % queue_size] = kk_atomic_load_relaxed(q->q + ((head + i) % queue_size));
        }

        if (num_to_grab == 0 || kk_atomic_cas_strong_acq_rel(&q->head, &head, head + num_to_grab)) {
            *out_buf_head += num_to_grab;
            return num_to_grab;
        }
    }
}
