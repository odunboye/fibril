#include "fibril_worker.h"
#include <string.h>

#define FW_MAX_REQUEST ((size_t)277) /* Includes the rejected 256-byte body boundary. */
#define FW_MAX_VALIDATED ((size_t)276)
typedef struct {
  const unsigned char *input;
  size_t input_length, consumed, produced;
  unsigned char validated[FW_MAX_VALIDATED];
} FWorkerInput;
static int request_read(void *opaque) {
  FWorkerInput *input = opaque;
  return input->consumed == input->input_length ? -1 : input->input[input->consumed++];
}
static int validated_write(void *opaque, unsigned char byte) {
  FWorkerInput *input = opaque;
  if (input->produced == sizeof(input->validated)) return -1;
  input->validated[input->produced++] = byte; return 0;
}
/* This is private validation buffering, never a client acknowledgement. */
static int validated_flush(void *opaque) { (void)opaque; return 0; }

FWorkerResult fibril_worker_enqueue(FQueue *queue,
                                   const unsigned char *tenant, size_t tenant_length,
                                   const unsigned char *request, size_t request_length) {
  FWorkerResult result = {FW_INVALID_ARGUMENT, F_BINARY_OK, 0, 0, 0};
  if (!queue || !tenant || !tenant_length || tenant_length > 128 || (!request && request_length))
    return result;
  if (request_length > FW_MAX_REQUEST) { result.status = FW_REJECTED; return result; }
  FWorkerInput input = {request, request_length, 0, 0, {0}};
  FByteAdapters host = {request_read, validated_write, validated_flush, &input};
  FBinaryResult validation = fibril_program_binary_embed(&host);
  result.validation_status = validation.status;
  if (validation.status != F_BINARY_OK) {
    result.status = validation.status == F_BINARY_REJECTED ? FW_REJECTED : FW_INTERNAL;
    return result;
  }
  /* Fail closed on a mismatched validator, partial output, trailing input, or
     future protocol drift. Never use output before the complete run succeeds. */
  if (input.consumed != request_length || input.produced < 22 ||
      input.produced != request_length ||
      memcmp(input.validated, "FV01", 4) || memcmp(request, "FQ01", 4) ||
      input.validated[20] != input.produced - 21 ||
      memcmp(input.validated + 4, request + 4, request_length - 4)) {
    result.status = FW_INTERNAL; return result;
  }
  /* Persist the complete canonical request, including its protocol version,
     rather than dropping information needed by future replay/migration rules. */
  memcpy(input.validated, "FQ01", 4);
  FQueueRequest enqueue = {tenant, input.validated + 4, input.validated,
                           tenant_length, 16, input.produced};
  FQueueResult queued = fibril_queue_enqueue(queue, &enqueue, &result.id, &result.created);
  result.sqlite_code = queued.sqlite_code;
  if (queued.status == FQ_OK) result.status = FW_OK;
  else if (queued.status == FQ_CONFLICT) result.status = FW_CONFLICT;
  else if (queued.status == FQ_BUSY) result.status = FW_BUSY;
  else if (queued.status == FQ_STORAGE) result.status = FW_STORAGE;
  else result.status = FW_INTERNAL;
  /* The queue API also resets these on failure; retain a fail-closed boundary
     if a future adapter accidentally supplies metadata alongside an error. */
  if (result.status != FW_OK) { result.id = 0; result.created = 0; }
  return result;
}
