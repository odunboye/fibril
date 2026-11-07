/* Measurement adapter only: no JSON/header grammar, no budget changes. */
#define fibril_native_binary_run original_binary_run
#include "fibril_binary_runtime.c"
#undef fibril_native_binary_run
static size_t consumed, accepted, flushes, requests_used, capacity_used;
static int measured_read(void *unused) {
  (void)unused;
  int byte = fgetc(stdin);
  if (byte != EOF) { consumed++; return byte; }
  return ferror(stdin) ? -2 : -1;
}
static int measured_write(void *unused, unsigned char byte) {
  (void)unused;
  if (fputc(byte, stdout) == EOF) return -1;
  accepted++; return 0;
}
static int measured_flush(void *unused) {
  (void)unused; flushes++;
  return fflush(stdout) == 0 ? 0 : -1;
}
static FByteStatus measured_body(FByteSession *session, void *opaque) {
  size_t requests = session->requests, capacity = session->capacity;
  FByteStatus status = binary_body(session, opaque);
  requests_used = requests - session->requests;
  capacity_used = capacity - session->capacity;
  return status;
}
int fibril_native_binary_run(FEval entry, size_t requests, size_t capacity) {
  FRuntime runtime = {0};
  FBinaryContext context = {&runtime, entry, FB_OK, 0, 0};
  FByteStatus status = fibril_bytes_run_with(requests, capacity,
    (FByteAdapters){measured_read, measured_write, measured_flush, NULL}, measured_body, &context);
  fprintf(stderr, "PROFILE %zu %zu %zu %zu %zu %zu %zu %zu %zu %zu %zu\n",
    runtime.steps, iteration_peak, runtime.bytes, iteration_callbacks,
    iteration_reads, iteration_writes, consumed, accepted, flushes, requests_used, capacity_used);
  return binary_finish(&runtime, &context, status);
}
