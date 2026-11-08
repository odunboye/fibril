/* Experimental enqueue-only worker boundary; link the checked queue validator. */
#ifndef FIBRIL_WORKER_H
#define FIBRIL_WORKER_H
#include "fibril_binary_embed.h"
#include "fibril_queue.h"

typedef enum {
  FW_OK = 0, FW_INVALID_ARGUMENT, FW_REJECTED, FW_INTERNAL,
  FW_CONFLICT, FW_BUSY, FW_STORAGE
} FWorkerStatus;
typedef struct {
  FWorkerStatus status;
  FBinaryStatus validation_status;
  int sqlite_code;
  int64_t id;
  int created;
} FWorkerResult;
/* Tenant comes from the trusted authenticated host context, NOT request bytes.
   Request v1: FQ01 + 16 opaque key bytes + one length octet (1..255)
   + exactly that many opaque payload bytes + EOF.
   The linked examples/modules/queue-worker validator must be the checked one.
   Validation output stays in a bounded private buffer. Only FW_OK signals a
   committed row (created=0 is an identical retry); all failures return id=0.
   No network/output callback is made, no automatic retry or dispatch occurs.
   Borrowed buffers must remain immutable/alive throughout the synchronous call. */
FWorkerResult fibril_worker_enqueue(FQueue *queue,
                                   const unsigned char *tenant, size_t tenant_length,
                                   const unsigned char *request, size_t request_length);
#endif
