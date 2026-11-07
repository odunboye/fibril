/* Observer/adapter harness for genuinely checked/emitted source. All runtime
   files are private copies; only counters are inserted, never budget changes. */
#include <assert.h>
#include "fibril_binary_runtime.c"
#define main checked_main
#include "program.c"
#undef main

typedef struct { size_t position, length, writes, flushes; const char *mode; } Host;
static const unsigned char view_input[] = {126,0,255,195,40,128,254,127,97,98,99};
static const unsigned char view_payload[] = {0,255,195,40,128};
static int view_mode(const Host *h) {
  return !strcmp(h->mode, "views-done") || !strcmp(h->mode, "views-exhausted");
}
static int test_read(void *opaque) {
  Host *h = opaque;
  if (!strcmp(h->mode, "read-error") && h->position + 2 >= h->length) return -2;
  if (h->position == h->length) return -1;
  if (view_mode(h)) {
    assert(h->position < sizeof(view_input));
    return view_input[h->position++];
  }
  h->position++;
  return strcmp(h->mode, "eof") && (h->position == h->length ||
    (!strcmp(h->mode, "two") && h->position == 1024)) ? ':' : 'a';
}
static int test_write(void *opaque, unsigned char byte) {
  Host *h = opaque;
  if (view_mode(h)) {
    assert(h->writes <= sizeof(view_payload));
    unsigned char expected = h->writes ? view_payload[h->writes - 1] :
      (!strcmp(h->mode, "views-done") ? 'D' : 'E');
    assert(byte == expected);
  }
  (void)byte;
  if (!strcmp(h->mode, "write-error") && h->writes == 1) return -1;
  h->writes++; return 0;
}
static int test_flush(void *opaque) {
  Host *h = opaque; h->flushes++;
  return !strcmp(h->mode, "flush-error") ? -1 : 0;
}
static size_t requests_used, capacity_used;
static FByteStatus observed_body(FByteSession *session, void *opaque) {
  FByteStatus status = binary_body(session, opaque);
  requests_used = 4096 - session->requests;
  capacity_used = 8388608 - session->capacity;
  return status;
}
int main(int argc, char **argv) {
  if (argc == 1) return checked_main();
  if (argc != 3) return 2;
  Host h = {0, (size_t)strtoul(argv[2], NULL, 10), 0, 0, argv[1]};
  FRuntime r = {0};
  FBinaryContext context = {&r, fibril_expr_0, FB_OK, 0, 0};
  FByteStatus status = fibril_bytes_run_with(4096, 8388608,
    (FByteAdapters){test_read, test_write, test_flush, &h}, observed_body, &context);
  printf("METRICS %zu %zu %zu %zu %zu\n", iteration_reads, iteration_writes,
    h.flushes, h.length - h.position, h.writes);
  if (status == FB_OK && !r.error) puts("OK");
  else printf("ERROR %s\n", r.error ? r.error : binary_error(status));
  printf("BUDGET %zu %zu\n", requests_used, capacity_used);
  printf("NATIVE %zu %zu %zu %zu\n", r.steps, iteration_peak, r.bytes, iteration_callbacks);
  /* Session teardown has happened; never inspect arena views here. */
  while (r.allocations) { FAllocation *next = r.allocations->next; free(r.allocations); r.allocations = next; }
  return 0;
}
