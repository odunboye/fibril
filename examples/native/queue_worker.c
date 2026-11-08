/* Local trusted-host demonstration, NOT an authenticated network service.
   Tenant is supplied by the operator, never read from the untrusted packet. */
#include "fibril_worker.h"
#include <inttypes.h>
#include <stdio.h>
#include <string.h>

int main(int argc, char **argv) {
  if (argc != 3) {
    fprintf(stderr, "usage: queue-worker PRIVATE_DATABASE TRUSTED_TENANT < request.bin\n");
    return 2;
  }
  size_t tenant_length = strlen(argv[2]);
  if (!tenant_length || tenant_length > 128) {
    fprintf(stderr, "queue-worker: invalid tenant scope\n"); return 2;
  }
  /* Read a complete bounded request before invoking checked code. EOF here is
     an explicit local CLI framing rule, not network disconnect semantics. */
  unsigned char request[278];
  size_t length = fread(request, 1, sizeof(request), stdin);
  if (ferror(stdin) || length == sizeof(request)) {
    fprintf(stderr, "queue-worker: input failure or request too large\n"); return 2;
  }
  FQueue *queue = NULL;
  FQueueResult opened = fibril_queue_open(argv[1], &queue);
  if (opened.status != FQ_OK) {
    fprintf(stderr, "queue-worker: open status %d (sqlite %d)\n", opened.status, opened.sqlite_code);
    return 1;
  }
  FWorkerResult result = fibril_worker_enqueue(queue, (const unsigned char *)argv[2],
                                             tenant_length, request, length);
  fibril_queue_close(queue);
  if (result.status != FW_OK) {
    fprintf(stderr, "queue-worker: enqueue status %d (sqlite %d)\n", result.status, result.sqlite_code);
    return 1;
  }
  /* A failed acknowledgement does not undo COMMIT. Retry the same key/payload;
     do not manufacture a new key or interpret this as an SMTP delivery result. */
  if (printf("{\"status\":\"queued\",\"id\":%" PRId64 ",\"created\":%s}\n",
             result.id, result.created ? "true" : "false") < 0 || fflush(stdout) == EOF)
    return 1;
  return 0;
}
