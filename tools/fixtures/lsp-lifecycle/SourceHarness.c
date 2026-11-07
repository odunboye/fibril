/* Adapter around genuinely checked/emitted source, not a lifecycle model. */
#include <assert.h>
#include "fibril_binary_runtime.c"
#define main checked_main
#include "program.c"
#undef main

typedef struct { size_t reads, writes, flushes; unsigned char output[4096]; } Host;
static int test_read(void *opaque) { ((Host *)opaque)->reads++; return -1; }
static int test_write(void *opaque, unsigned char byte) {
  Host *h = opaque;
  assert(h->writes < sizeof h->output);
  h->output[h->writes++] = byte;
  return 0;
}
static int test_flush(void *opaque) { ((Host *)opaque)->flushes++; return 0; }
static size_t requests_used, capacity_used;
static FByteStatus observed_body(FByteSession *session, void *opaque) {
  FByteStatus status = binary_body(session, opaque);
  requests_used = 4096 - session->requests;
  capacity_used = 8388608 - session->capacity;
  return status;
}
int main(int argc, char **argv) {
  (void)argv;
  if (argc == 1) return checked_main();
  if (argc != 2) return 2;
  Host h = {0};
  FRuntime r = {0};
  FBinaryContext context = {&r, fibril_expr_0, FB_OK, 0, 0};
  FByteStatus status = fibril_bytes_run_with(4096, 8388608,
    (FByteAdapters){test_read, test_write, test_flush, &h}, observed_body, &context);
  printf("METRICS %zu %zu %zu %zu %zu\n", h.reads, h.writes, h.flushes,
    requests_used, capacity_used);
  printf("OUTPUT [");
  for (size_t i = 0; i < h.writes; i++) printf("%s%u", i ? ", " : "", h.output[i]);
  puts("]");
  printf("COST %zu %zu\n", r.steps, r.bytes);
  int failed = status != FB_OK || r.error;
  if (failed) printf("ERROR %s\n", r.error ? r.error : binary_error(status));
  else puts("OK");
  while (r.allocations) { FAllocation *next = r.allocations->next; free(r.allocations); r.allocations = next; }
  return failed;
}
