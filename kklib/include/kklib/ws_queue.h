#pragma once
#ifndef KK_WS_QUEUE_H
#define KK_WS_QUEUE_H

enum kk_ws_queue_constants {
    queue_size_pow = 10, //power of 2
    queue_size = 1 << queue_size_pow,
};

typedef enum kk_ws_queue_type {
    lifo,
    fifo
} kk_ws_queue_type_e;

typedef struct kk_ws_queue_fifo_s {
    _Alignas(64) kk_atomic(size_t) head;
    _Alignas(64) kk_atomic(size_t) tail;
    _Alignas(64) kk_atomic(uintptr_t) q[queue_size];
} kk_ws_queue_fifo_t;

typedef struct kk_ws_queue_lifo_s {
} kk_ws_queue_lifo_t;

typedef struct kk_ws_queue_s {
    kk_ws_queue_type_e type;
    union {
        kk_ws_queue_lifo_t lifo_q;
        kk_ws_queue_fifo_t fifo_q;
    };
} kk_ws_queue_t;

kk_decl_export kk_ws_queue_t* kk_ws_queue_alloc(kk_ws_queue_type_e type, kk_context_t* ctx);
kk_decl_export void kk_ws_queue_free(const kk_ws_queue_t* q, kk_context_t* ctx);

kk_decl_export bool kk_ws_queue_put(kk_ws_queue_t* q, void* task);
kk_decl_export void* kk_ws_queue_pop(kk_ws_queue_t* q);
kk_decl_export size_t kk_ws_queue_steal(kk_ws_queue_t* from, kk_ws_queue_t* to);
kk_decl_export size_t kk_ws_queue_grab(kk_ws_queue_t* q, uintptr_t* out);

#endif //include guard
