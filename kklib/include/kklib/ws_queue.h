#pragma once
#ifndef KK_WS_QUEUE_H
#define KK_WS_QUEUE_H

enum kk_ws_queue_constants {
    queue_size_pow = 10, //power of 2
    queue_size = 1 << queue_size_pow,
    num_to_steal = queue_size / 2 ,
};

typedef struct kk_ws_queue_s {
    kk_atomic(size_t) head;
    kk_atomic(size_t) tail;
    kk_atomic(uintptr_t) q[queue_size];
} kk_ws_queue_t;

kk_decl_export kk_ws_queue_t* kk_ws_queue_alloc(kk_context_t* ctx);
kk_decl_export void kk_ws_queue_free(const kk_ws_queue_t* q, kk_context_t* ctx);

kk_decl_export bool kk_ws_queue_put(kk_ws_queue_t* q, void* task);
kk_decl_export void* kk_ws_queue_pop(kk_ws_queue_t* q);
kk_decl_export size_t kk_ws_queue_steal(kk_ws_queue_t* q, kk_atomic(uintptr_t)* out_buf, size_t* out_buf_head);

#endif //include guard
