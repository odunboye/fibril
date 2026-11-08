/* Trusted C adversarial fixtures: not evidence of Fibril source typing. */
#include "fibril_runtime.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>

typedef struct {
  unsigned char output[128];
  size_t length, writes, flushes, fail_write;
  int fail_flush, nested;
  FNativeHost *mutate;
} Sink;

static FValue *unit(FRuntime *r, FEnv *env) { (void)env; return f_unit(r); }
static FValue *pure(FRuntime *r, FEnv *env) { return f_pure(r, env, unit); }
static FValue *text(FRuntime *r, FEnv *env) {
  static const unsigned char bytes[] = { 'h', 0xc3, 0xa9 };
  (void)env; return f_literal(r, bytes, sizeof(bytes));
}
static FValue *empty(FRuntime *r, FEnv *env) {
  static const unsigned char bytes[] = { 0 };
  (void)env; return f_literal(r, bytes, 0);
}
static FValue *nul_text(FRuntime *r, FEnv *env) {
  static const unsigned char bytes[] = { 'x', 0, 'y' };
  (void)env; return f_literal(r, bytes, sizeof(bytes));
}
static FValue *write_text(FRuntime *r, FEnv *env) { return f_write(r, env, text); }
static FValue *write_empty(FRuntime *r, FEnv *env) { return f_write(r, env, empty); }
static FValue *write_nul(FRuntime *r, FEnv *env) { return f_write(r, env, nul_text); }
static FValue *nul_cont(FRuntime *r, FEnv *env) { return f_lambda(r, env, 0, write_nul); }
static FValue *late_nul(FRuntime *r, FEnv *env) { return f_bind(r, env, write_text, nul_cont); }
static FValue *boolean(FRuntime *r, FEnv *env) { (void)env; return f_bool(r, 1); }
static FValue *bad_final(FRuntime *r, FEnv *env) { return f_pure(r, env, boolean); }
static FValue *bad_cont(FRuntime *r, FEnv *env) { return f_lambda(r, env, 0, bad_final); }
static FValue *late_bad_final(FRuntime *r, FEnv *env) { return f_bind(r, env, write_text, bad_cont); }
static FValue *missing(FRuntime *r, FEnv *env) { (void)r; (void)env; return NULL; }
static FValue *depth(FRuntime *r, FEnv *env) { (void)env; return f_global(r, depth); }
static FValue *resource(FRuntime *r, FEnv *env) { return f_with_input(r, env, text, pure); }
static FValue *input(FRuntime *r, FEnv *env) { (void)env; return f_read_line(r); }
static FValue *empty_cont(FRuntime *r, FEnv *env) { return f_lambda(r, env, 0, write_empty); }
static FValue *two_lines(FRuntime *r, FEnv *env) { return f_bind(r, env, write_text, empty_cont); }

static int flush(void *context) {
  Sink *s = context; s->flushes++; return s->fail_flush;
}
static int write_bytes(void *context, const unsigned char *bytes, size_t length) {
  Sink *s = context;
  s->writes++;
  if (s->mutate) { s->mutate->write = NULL; s->mutate->flush = NULL; }
  if (s->nested) {
    Sink inner = {0};
    FNativeHost host = { &inner, write_bytes, flush };
    FNativeResult result = fibril_native_embed(write_text, &host);
    assert(result.status == F_NATIVE_OK && inner.length == 4);
  }
  if (s->fail_write == s->writes) return -1;
  assert(length <= sizeof(s->output) - s->length);
  memcpy(s->output + s->length, bytes, length); s->length += length;
  return 0;
}

int main(int argc, char **argv) {
  assert(argc == 2);
  Sink sink = {0};
  FNativeHost host = { &sink, write_bytes, flush };
  FNativeResult result;
  const char *name = argv[1];
  if (!strcmp(name, "invalid")) {
    result = fibril_native_embed(NULL, &host);
    assert(result.status == F_NATIVE_INVALID_ARGUMENT);
    result = fibril_native_embed(pure, NULL);
    assert(result.status == F_NATIVE_INVALID_ARGUMENT);
    host.write = NULL;
    result = fibril_native_embed(pure, &host);
    assert(result.status == F_NATIVE_INVALID_ARGUMENT);
    host.write = write_bytes; host.flush = NULL;
    result = fibril_native_embed(pure, &host);
    assert(result.status == F_NATIVE_INVALID_ARGUMENT);
    assert(sink.writes == 0 && sink.flushes == 0);
    return 0;
  }
  FEval entry = write_text;
  FNativeStatus expected = F_NATIVE_OK;
  if (!strcmp(name, "pure")) entry = pure;
  else if (!strcmp(name, "empty")) entry = write_empty;
  else if (!strcmp(name, "two-lines")) entry = two_lines;
  else if (!strcmp(name, "write-failure")) { sink.fail_write = 1; expected = F_NATIVE_WRITE_ERROR; }
  else if (!strcmp(name, "newline-failure")) { sink.fail_write = 2; expected = F_NATIVE_WRITE_ERROR; }
  else if (!strcmp(name, "flush-failure")) { sink.fail_flush = 1; expected = F_NATIVE_FLUSH_ERROR; }
  else if (!strcmp(name, "late-nul")) { entry = late_nul; expected = F_NATIVE_PROGRAM_ERROR; }
  else if (!strcmp(name, "late-bad-final")) { entry = late_bad_final; expected = F_NATIVE_PROGRAM_ERROR; }
  else if (!strcmp(name, "missing")) { entry = missing; expected = F_NATIVE_PROGRAM_ERROR; }
  else if (!strcmp(name, "depth")) { entry = depth; expected = F_NATIVE_PROGRAM_ERROR; }
  else if (!strcmp(name, "resource")) { entry = resource; expected = F_NATIVE_PROGRAM_ERROR; }
  else if (!strcmp(name, "input")) { entry = input; expected = F_NATIVE_PROGRAM_ERROR; }
  else if (!strcmp(name, "nested")) sink.nested = 1;
  else if (!strcmp(name, "mutated-table")) sink.mutate = &host;
  else assert(!strcmp(name, "text") || !strcmp(name, "repeat"));
  result = fibril_native_embed(entry, &host);
  assert(result.status == expected);
  assert((result.message == NULL) == (expected == F_NATIVE_OK));
  if (expected == F_NATIVE_PROGRAM_ERROR) {
    assert(sink.writes == 0 && sink.flushes == 0 && sink.length == 0);
    /* Error text survives arena teardown. */
    assert(strlen(result.message) > 0);
  } else if (expected == F_NATIVE_WRITE_ERROR) {
    assert(sink.writes == sink.fail_write && sink.flushes == 0);
    assert(sink.length == (sink.fail_write == 1 ? 0 : 3));
  } else {
    assert(sink.flushes == 1);
    size_t length = entry == pure ? 0 : entry == write_empty ? 1 : entry == two_lines ? 5 : 4;
    static const unsigned char output[] = { 'h', 0xc3, 0xa9, '\n', '\n' };
    assert(sink.length == length);
    if (entry == write_empty) assert(sink.output[0] == '\n');
    else if (length) assert(!memcmp(sink.output, output, length));
  }
  /* No state leaks between runs, even after a callback/program failure. */
  for (size_t i = 0; i < (!strcmp(name, "repeat") ? 1000u : 1u); i++) {
    Sink fresh = {0};
    FNativeHost next = { &fresh, write_bytes, flush };
    result = fibril_native_embed(write_text, &next);
    assert(result.status == F_NATIVE_OK && fresh.length == 4 && fresh.flushes == 1);
  }
  return 0;
}
