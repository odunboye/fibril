/* Genuinely checked/emitted source; private runtime copies add counters only. */
#include <assert.h>
#include "fibril_binary_runtime.c"
#define main checked_main
#include "program.c"
#undef main

typedef struct { size_t position, length, writes, flushes; unsigned char input[128], output[1024]; } Host;
static int test_read(void *opaque) {
  Host *h = opaque;
  return h->position == h->length ? -1 : h->input[h->position++];
}
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
  if (argc == 1) return checked_main();
  if (argc != 2) return 2;
  Host h = {0};
  h.length = strlen(argv[1]) / 2;
  assert(h.length <= sizeof h.input);
  for (size_t i = 0; i < h.length; i++) {
    unsigned int byte;
    assert(sscanf(argv[1] + 2*i, "%2x", &byte) == 1);
    h.input[i] = (unsigned char)byte;
  }
  FRuntime r = {0};
  FBinaryContext context = {&r, fibril_expr_0, FB_OK, 0, 0};
  FByteStatus status = fibril_bytes_run_with(4096, 8388608,
    (FByteAdapters){test_read, test_write, test_flush, &h}, observed_body, &context);
  printf("METRICS %zu %zu %zu %zu %zu\n", iteration_reads, iteration_writes,
    h.flushes, h.length - h.position, h.writes);
  printf("OUTPUT [");
  for (size_t i = 0; i < h.writes; i++) printf("%s%u", i ? ", " : "", h.output[i]);
  puts("]");
  if (status == FB_OK && !r.error) puts("OK");
  else printf("ERROR %s\n", r.error ? r.error : binary_error(status));
  printf("BUDGET %zu %zu\n", requests_used, capacity_used);
  printf("NATIVE %zu %zu %zu %zu\n", r.steps, iteration_peak, r.bytes, iteration_callbacks);
  while (r.allocations) { FAllocation *next = r.allocations->next; free(r.allocations); r.allocations = next; }
  return 0;
}
