/* Public embedding API only; trusted adversarial fixtures, not typing proofs. */
#include "fibril_binary_embed.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  size_t reads, writes, flushes, length;
  int mode;
  FByteAdapters *mutate;
} Host;
static const unsigned char payload[] = {0, 255, 13, 10};
static int read_host(void *opaque) {
  Host *h = opaque;
  if (h->mode == 4 && h->reads == 2) return -2;
  if (h->mode == 14) return 256;
  if (h->mode == 15) return -3;
  if (h->mutate) { h->mutate->read = NULL; h->mutate->write = NULL; h->mutate->flush = NULL; }
  if (h->reads == h->length) return -1;
  return payload[h->reads++];
}
static int write_host(void *opaque, unsigned char byte) {
  Host *h = opaque;
  if (h->mode == 5 && h->writes == 1) return -1;
  if (h->mode == 16) return 1;
  assert(h->writes < sizeof(payload) && byte == payload[h->writes]);
  h->writes++; return 0;
}
static int flush_host(void *opaque) {
  Host *h = opaque; h->flushes++;
  return h->mode == 6 ? -1 : h->mode == 17 ? 1 : 0;
}
static FValue *data(FRuntime *r, FEnv *e) { (void)e; return f_bytes_literal(r, payload, sizeof(payload)); }
static FValue *unit(FRuntime *r, FEnv *e) { (void)e; return f_unit(r); }
static FValue *pure(FRuntime *r, FEnv *e) { return f_pure(r, e, unit); }
static FValue *capacity(FRuntime *r, FEnv *e) { return f_bytes_length(r, e, data); }
static FValue *read_normal(FRuntime *r, FEnv *e) { return f_read_bytes(r, e, capacity); }
static FValue *consume(FRuntime *r, FEnv *e) { return f_variable(r, e, 0); }
static FValue *write_payload(FRuntime *r, FEnv *e) { return f_write_bytes(r, e, consume); }
static FValue *chunk(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, write_payload); }
static FValue *choose(FRuntime *r, FEnv *e) {
  FEval branches[] = {pure, chunk}; return f_variant_case(r, e, consume, 2, branches);
}
static FValue *next(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, choose); }
static FValue *echo(FRuntime *r, FEnv *e) { return f_bind(r, e, read_normal, next); }
static FValue *flush(FRuntime *r, FEnv *e) { (void)e; return f_flush_bytes(r); }
static FValue *zero(FRuntime *r, FEnv *e) { (void)e; return f_nat_zero(r); }
static FValue *read_zero(FRuntime *r, FEnv *e) { return f_read_bytes(r, e, zero); }
static FValue *bad_main(FRuntime *r, FEnv *e) { return f_pure(r, e, data); }
static FValue *write_direct(FRuntime *r, FEnv *e) { return f_write_bytes(r, e, data); }
static FValue *bad_next(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, unit); }
static FValue *bad_later(FRuntime *r, FEnv *e) { return f_bind(r, e, write_direct, bad_next); }
static FValue *reject(FRuntime *r, FEnv *e) { (void)e; return f_reject_bytes(r); }
static FValue *text_input(FRuntime *r, FEnv *e) { (void)e; return f_read_line(r); }
static FValue *depth(FRuntime *r, FEnv *e) { (void)e; return f_global(r, depth); }
int main(int argc, char **argv) {
  assert(argc == 2);
  int mode = atoi(argv[1]);
  Host h = {0, 0, 0, 4, mode, NULL};
  FByteAdapters adapters = {read_host, write_host, flush_host, &h};
  size_t requests = 2, bytes = 8;
  FEval entry = echo;
  FBinaryResult result;
  if (mode == 20) {
    result = fibril_native_binary_embed(NULL, 0, 0, &adapters);
    assert(result.status == F_BINARY_INVALID_ARGUMENT);
    result = fibril_native_binary_embed(pure, 0, 0, NULL);
    assert(result.status == F_BINARY_INVALID_ARGUMENT);
    adapters.read = NULL;
    result = fibril_native_binary_embed(pure, 0, 0, &adapters);
    assert(result.status == F_BINARY_INVALID_ARGUMENT);
    adapters.read = read_host; adapters.write = NULL;
    result = fibril_native_binary_embed(pure, 0, 0, &adapters);
    assert(result.status == F_BINARY_INVALID_ARGUMENT);
    adapters.write = write_host; adapters.flush = NULL;
    result = fibril_native_binary_embed(pure, 0, 0, &adapters);
    assert(result.status == F_BINARY_INVALID_ARGUMENT && result.transport_status == FB_OK);
    assert(!h.reads && !h.writes && !h.flushes);
    return 0;
  }
  if (mode == 1 || mode == 2) { h.length = 2; bytes = mode == 1 ? 6 : 5; }
  if (mode == 3) { h.length = 0; requests = 1; bytes = 4; }
  if (mode == 6 || mode == 17) { entry = pure; requests = 0; bytes = 0; }
  if (mode == 7) { entry = flush; requests = 1; bytes = 0; }
  if (mode == 8) { entry = read_zero; requests = 1; bytes = 0; }
  if (mode == 9) entry = bad_main;
  if (mode == 10) requests = 0;
  if (mode == 11) entry = bad_later;
  if (mode == 12) requests = 100001;
  if (mode == 13) entry = reject;
  if (mode == 18) bytes = 8388609;
  if (mode == 19) h.mutate = &adapters;
  if (mode == 21) entry = text_input;
  if (mode == 22) entry = depth;
  result = fibril_native_binary_embed(entry, requests, bytes, &adapters);
  if (mode == 0 || mode == 1 || mode == 3 || mode == 7 || mode == 19) {
    assert(result.status == F_BINARY_OK && result.message == NULL && result.transport_status == FB_OK);
    assert(h.writes == (mode == 3 || mode == 7 ? 0 : h.length));
    assert(h.flushes == (mode == 7 ? 2 : 1));
  } else if (mode == 9 || mode == 11 || mode == 13 || mode == 21 || mode == 22) {
    assert(result.status == F_BINARY_PROGRAM_ERROR && result.transport_status == FB_OK);
    assert(result.message && strlen(result.message) > 0 && !h.flushes);
    assert(h.writes == (mode == 11 ? 4 : 0));
  } else {
    FByteStatus expected = mode == 2 ? FB_BYTE_LIMIT : mode == 4 ? FB_READ_FAILED :
      mode == 5 ? FB_WRITE_FAILED : mode == 6 ? FB_FLUSH_FAILED :
      mode == 8 ? FB_ZERO_READ : mode == 10 ? FB_REQUEST_LIMIT :
      mode == 12 || mode == 18 ? FB_ADMISSION : FB_ADAPTER_VIOLATION;
    assert(result.status == F_BINARY_TRANSPORT_ERROR && result.transport_status == expected);
    assert(result.message && strlen(result.message) > 0);
    assert(h.flushes == (mode == 6 || mode == 17 ? 1 : 0));
    if (mode == 2) assert(h.reads == 2 && !h.writes);
    if (mode == 12 || mode == 18) assert(!h.reads && !h.writes);
  }
  assert(result.read_prefix == (mode == 4 ? 2u : 0u));
  assert(result.write_prefix == (mode == 5 ? 1u : 0u));
  for (size_t i = 0; i < 100; i++) {
    Host fresh = {0, 0, 0, 4, 0, NULL};
    FByteAdapters host = {read_host, write_host, flush_host, &fresh};
    result = fibril_native_binary_embed(echo, 2, 8, &host);
    assert(result.status == F_BINARY_OK && fresh.writes == 4 && fresh.flushes == 1);
  }
  return 0;
}
