/* Experimental trusted POSIX/SQLite enqueue-only outbox, not a source FFI. */
#ifndef FIBRIL_QUEUE_H
#define FIBRIL_QUEUE_H
#include <stddef.h>
#include <stdint.h>

typedef struct FQueue FQueue;
typedef enum {
  FQ_OK = 0, FQ_INVALID, FQ_CONFLICT, FQ_NOT_FOUND, FQ_BUFFER_SMALL,
  FQ_BUSY, FQ_STORAGE, FQ_UNSUPPORTED
} FQueueStatus;
typedef struct {
  FQueueStatus status;
  /* Extended SQLite error code, or 0 for non-SQLite validation failures. */
  int sqlite_code;
} FQueueResult;
typedef struct {
  const unsigned char *tenant, *key, *payload;
  size_t tenant_length, key_length, payload_length;
} FQueueRequest;

/* Local filesystem only; SQLite >= 3.35, WAL and synchronous=FULL required.
   Parent directory/path must be trusted, stable and owned by the host. No URI,
   in-memory database, symlink or permissive/non-owner database is accepted.
   Newly created database files use 0600. No logs, retries or process-global IO.
   A handle is sequential, may not be used after fork, and must not be shared
   concurrently. The host must authenticate/authorize tenant and bound requests. */
FQueueResult fibril_queue_open(const char *path, FQueue **out);
void fibril_queue_close(FQueue *queue);
/* Tenant/key: 1..128 opaque bytes each; payload: 1..65536 opaque bytes.
   Same tenant/key + identical payload returns the existing ID with created=0.
   Different payload returns CONFLICT; success only after COMMIT. IDs/created
   are reset to zero on failure. A failed COMMIT may have an uncertain outcome;
   retrying the SAME request is safe, inventing a new key is not equivalent. */
FQueueResult fibril_queue_enqueue(FQueue *, const FQueueRequest *, int64_t *id, int *created);
/* Copies a committed payload into host storage. No internal pointer escapes.
   On BUFFER_SMALL, length is required size and id identifies the row; no copy.
   Other failures reset id/length. This is not an authorization check. */
FQueueResult fibril_queue_get(FQueue *, const unsigned char *tenant, size_t tenant_length,
                            const unsigned char *key, size_t key_length,
                            unsigned char *payload, size_t capacity,
                            size_t *length, int64_t *id);
#endif
