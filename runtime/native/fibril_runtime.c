/* Experimental runtime for generated Fibril C. No ownership or safety proof. */
#include "fibril_runtime.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define F_MAX_BYTES ((size_t)16777216)
#define F_MAX_STEPS ((size_t)100000)
#define F_MAX_DEPTH ((size_t)512)
#define F_MAX_ACTIONS ((size_t)64)

/* Keep every payload suitably aligned for all C object types. */
typedef union FAllocation { union FAllocation *next; max_align_t alignment; } FAllocation;
typedef struct FThunk FThunk;
typedef struct FAction { const unsigned char *bytes; size_t length; struct FAction *next; } FAction;
struct FRuntime { FAllocation *allocations; size_t bytes, steps, depth, actions; const char *error; FAction *head, *tail; };
struct FEnv { FThunk *value; FEnv *tail; };
typedef enum { V_UNIT, V_ERASED, V_BOOL, V_STRING, V_CLOSURE, V_NOMINAL, V_VARIANT, V_PURE, V_BIND, V_WRITE, V_READ } FTag;
struct FValue {
  FTag tag;
  union {
    struct { const unsigned char *bytes; size_t length; } string;
    int boolean;
    FThunk *nominal;
    struct { size_t tag; FThunk *payload; } variant;
    struct { FEval body; FEnv *env; int erased; } closure;
    struct { FThunk *first, *second; } io;
  } as;
};
struct FThunk { FEval code; FEnv *env; FValue *value; int state; };

static void fail(FRuntime *r, const char *message) { if (!r->error) r->error = message; }
static void *allocate(FRuntime *r, size_t size) {
  if (r->error) return NULL;
  if (size > SIZE_MAX - sizeof(FAllocation) || size > F_MAX_BYTES || r->bytes > F_MAX_BYTES - size) {
    fail(r, "native allocation budget exhausted"); return NULL;
  }
  FAllocation *p = malloc(sizeof(FAllocation) + size);
  if (!p) { fail(r, "native allocation failed"); return NULL; }
  p->next = r->allocations; r->allocations = p; r->bytes += size;
  return (void *)(p + 1);
}
static int enter(FRuntime *r) {
  if (r->error) return 0;
  if (r->steps >= F_MAX_STEPS || r->depth >= F_MAX_DEPTH) { fail(r, "native evaluation budget exhausted"); return 0; }
  r->steps++; r->depth++; return 1;
}
static FValue *evaluate(FRuntime *r, FEval code, FEnv *env) {
  if (!enter(r)) return NULL;
  FValue *result = code(r, env);
  r->depth--; return result;
}
static FValue *new_value(FRuntime *r, FTag tag) {
  FValue *v = allocate(r, sizeof(*v));
  if (v) { memset(v, 0, sizeof(*v)); v->tag = tag; }
  return v;
}
static FThunk *thunk(FRuntime *r, FEval code, FEnv *env) {
  FThunk *t = allocate(r, sizeof(*t));
  if (t) { t->code = code; t->env = env; t->value = NULL; t->state = 0; }
  return t;
}
static FThunk *ready(FRuntime *r, FValue *value) {
  if (!value) return NULL;
  FThunk *t = thunk(r, NULL, NULL);
  if (t) { t->value = value; t->state = 2; }
  return t;
}
static FValue *force(FRuntime *r, FThunk *t) {
  if (!t) { fail(r, "erased argument was forced"); return NULL; }
  if (t->state == 2) return t->value;
  if (t->state == 1) { fail(r, "cyclic native thunk"); return NULL; }
  t->state = 1;
  FValue *value = evaluate(r, t->code, t->env);
  if (!value) return NULL;
  t->value = value; t->state = 2; return value;
}
static FEnv *extend(FRuntime *r, FEnv *env, FThunk *value) {
  FEnv *next = allocate(r, sizeof(*next));
  if (next) { next->value = value; next->tail = env; }
  return next;
}
FValue *f_unit(FRuntime *r) { return new_value(r, V_UNIT); }
FValue *f_bool(FRuntime *r, int value) {
  FValue *v = new_value(r, V_BOOL);
  if (v) v->as.boolean = value != 0;
  return v;
}
FValue *f_erased(FRuntime *r) { return new_value(r, V_ERASED); }
FValue *f_literal(FRuntime *r, const unsigned char *bytes, size_t length) {
  FValue *v = new_value(r, V_STRING);
  if (v) { v->as.string.bytes = bytes; v->as.string.length = length; }
  return v;
}
FValue *f_variable(FRuntime *r, FEnv *env, size_t index) {
  while (env && index) { env = env->tail; index--; }
  if (!env) { fail(r, "invalid native variable"); return NULL; }
  return force(r, env->value);
}
FValue *f_lambda(FRuntime *r, FEnv *env, int erased, FEval body) {
  FValue *v = new_value(r, V_CLOSURE);
  if (v) { v->as.closure.body = body; v->as.closure.env = env; v->as.closure.erased = erased; }
  return v;
}
static FValue *apply_thunk(FRuntime *r, FValue *function, FThunk *argument) {
  if (!function || function->tag != V_CLOSURE) { fail(r, "native application expects a function"); return NULL; }
  FEnv *env = extend(r, function->as.closure.env, function->as.closure.erased ? NULL : argument);
  if (!env) return NULL;
  return evaluate(r, function->as.closure.body, env);
}
FValue *f_apply(FRuntime *r, FEnv *env, FEval function, FEval argument) {
  FValue *fun = evaluate(r, function, env);
  if (!fun || fun->tag != V_CLOSURE) { fail(r, "native application expects a function"); return NULL; }
  FThunk *arg = fun->as.closure.erased ? NULL : thunk(r, argument, env);
  if (!fun->as.closure.erased && !arg) return NULL;
  return apply_thunk(r, fun, arg);
}
FValue *f_append(FRuntime *r, FEnv *env, FEval left, FEval right) {
  FValue *a = evaluate(r, left, env);
  if (!a) return NULL;
  FValue *b = evaluate(r, right, env);
  if (!b || a->tag != V_STRING || b->tag != V_STRING) { fail(r, "native append expects strings"); return NULL; }
  if (a->as.string.length > SIZE_MAX - b->as.string.length) { fail(r, "native string length overflow"); return NULL; }
  size_t n = a->as.string.length + b->as.string.length;
  unsigned char *bytes = allocate(r, n ? n : 1);
  if (!bytes) return NULL;
  memcpy(bytes, a->as.string.bytes, a->as.string.length);
  memcpy(bytes + a->as.string.length, b->as.string.bytes, b->as.string.length);
  return f_literal(r, bytes, n);
}
FValue *f_bool_case(FRuntime *r, FEnv *env, FEval scrutinee, FEval yes, FEval no) {
  FValue *value = evaluate(r, scrutinee, env);
  if (!value || value->tag != V_BOOL) { fail(r, "native boolean case expects Bool"); return NULL; }
  return evaluate(r, value->as.boolean ? yes : no, env);
}
FValue *f_string_equal(FRuntime *r, FEnv *env, FEval left, FEval right) {
  FValue *a = evaluate(r, left, env);
  FValue *b = a ? evaluate(r, right, env) : NULL;
  if (!a || !b || a->tag != V_STRING || b->tag != V_STRING) { fail(r, "native equality expects strings"); return NULL; }
  return f_bool(r, a->as.string.length == b->as.string.length &&
                   memcmp(a->as.string.bytes, b->as.string.bytes, a->as.string.length) == 0);
}
FValue *f_nominal(FRuntime *r, FEnv *env, FEval value) {
  FValue *v = new_value(r, V_NOMINAL);
  if (!v) return NULL;
  v->as.nominal = thunk(r, value, env);
  return v->as.nominal ? v : NULL;
}
FValue *f_nominal_case(FRuntime *r, FEnv *env, FEval scrutinee, FEval branch) {
  FValue *v = evaluate(r, scrutinee, env);
  if (!v || v->tag != V_NOMINAL) { fail(r, "native nominal case expects a nominal value"); return NULL; }
  FValue *f = evaluate(r, branch, env);
  return f ? apply_thunk(r, f, v->as.nominal) : NULL;
}
FValue *f_variant(FRuntime *r, FEnv *env, size_t tag, FEval payload) {
  FValue *v = new_value(r, V_VARIANT);
  if (!v) return NULL;
  v->as.variant.tag = tag;
  if (payload) {
    v->as.variant.payload = thunk(r, payload, env);
    if (!v->as.variant.payload) return NULL;
  }
  return v;
}
FValue *f_variant_case(FRuntime *r, FEnv *env, FEval scrutinee, size_t count, const FEval *branches) {
  FValue *v = evaluate(r, scrutinee, env);
  if (!v || v->tag != V_VARIANT || v->as.variant.tag >= count) {
    fail(r, "native variant case expects an in-range variant"); return NULL;
  }
  FValue *branch = evaluate(r, branches[v->as.variant.tag], env);
  if (!branch) return NULL;
  return v->as.variant.payload ? apply_thunk(r, branch, v->as.variant.payload) : branch;
}
FValue *f_unit_case(FRuntime *r, FEnv *env, FEval scrutinee, FEval body) {
  FValue *value = evaluate(r, scrutinee, env);
  if (!value || value->tag != V_UNIT) { fail(r, "native unit case expects unit"); return NULL; }
  return evaluate(r, body, env);
}
static FValue *io1(FRuntime *r, FEnv *env, FTag tag, FEval first, FEval second) {
  FValue *v = new_value(r, tag); if (!v) return NULL;
  v->as.io.first = thunk(r, first, env);
  if (!v->as.io.first) return NULL;
  if (second) { v->as.io.second = thunk(r, second, env); if (!v->as.io.second) return NULL; }
  return v;
}
FValue *f_pure(FRuntime *r, FEnv *env, FEval value) { return io1(r, env, V_PURE, value, NULL); }
FValue *f_bind(FRuntime *r, FEnv *env, FEval action, FEval continuation) { return io1(r, env, V_BIND, action, continuation); }
FValue *f_write(FRuntime *r, FEnv *env, FEval text) { return io1(r, env, V_WRITE, text, NULL); }
FValue *f_read_line(FRuntime *r) { return new_value(r, V_READ); }

/* Build the complete action plan before writing anything to the host. */
static FThunk *plan(FRuntime *r, FValue *io) {
  if (!enter(r)) return NULL;
  FThunk *result = NULL;
  if (!io) fail(r, "missing native IO description");
  else if (io->tag == V_PURE) result = io->as.io.first;
  else if (io->tag == V_WRITE) {
    FValue *text = force(r, io->as.io.first);
    if (!text || text->tag != V_STRING) fail(r, "native write expects a string");
    else if (r->actions >= F_MAX_ACTIONS) fail(r, "native output action budget exhausted");
    else {
      FAction *item = allocate(r, sizeof(*item));
      if (item) {
        item->bytes = text->as.string.bytes; item->length = text->as.string.length; item->next = NULL;
        if (r->tail) r->tail->next = item; else r->head = item;
        r->tail = item; r->actions++; result = ready(r, f_unit(r));
      }
    }
  } else if (io->tag == V_BIND) {
    FValue *first = force(r, io->as.io.first);
    FThunk *value = first ? plan(r, first) : NULL;
    FValue *next = value ? force(r, io->as.io.second) : NULL;
    FValue *following = next ? apply_thunk(r, next, value) : NULL;
    if (following) result = plan(r, following);
  } else fail(r, "native program returned a non-IO value");
  r->depth--; return result;
}
/* Validate scalar UTF-8 and count decoded characters. Reject overlong forms,
   surrogates and values beyond U+10FFFF rather than inventing replacements. */
static int utf8_count(const unsigned char *bytes, size_t length, size_t *count) {
  size_t i = 0; *count = 0;
  while (i < length) {
    unsigned char c = bytes[i++]; size_t more; uint32_t value, minimum;
    if (c < 128) { (*count)++; continue; }
    if (c >= 194 && c <= 223) { more = 1; value = c & 31; minimum = 128; }
    else if (c >= 224 && c <= 239) { more = 2; value = c & 15; minimum = 2048; }
    else if (c >= 240 && c <= 244) { more = 3; value = c & 7; minimum = 65536; }
    else return 0;
    if (more > length - i) return 0;
    while (more--) {
      unsigned char next = bytes[i++];
      if ((next & 192) != 128) return 0;
      value = (value << 6) | (next & 63);
    }
    if (value < minimum || value > 0x10ffff || (value >= 0xd800 && value <= 0xdfff)) return 0;
    (*count)++;
  }
  return 1;
}
static FValue *read_result(FRuntime *r, size_t tag, FValue *payload) {
  FValue *v = new_value(r, V_VARIANT);
  if (!v) return NULL;
  v->as.variant.tag = tag;
  if (payload) { v->as.variant.payload = ready(r, payload); if (!v->as.variant.payload) return NULL; }
  return v;
}
static FValue *input_error(FRuntime *r, const char *message) {
  FValue *text = f_literal(r, (const unsigned char *)message, strlen(message));
  return text ? read_result(r, 2, text) : NULL;
}
static FValue *read_line(FRuntime *r, size_t limit) {
  if (fflush(stdout) == EOF) return input_error(r, "Console stdout flush failed");
  /* Admission caps limit at 8192, so this multiplication cannot overflow. */
  size_t capacity = limit * 4 + 2, length = 0; int overflow = 0, c;
  unsigned char *bytes = allocate(r, capacity);
  if (!bytes) return NULL;
  while ((c = fgetc(stdin)) != EOF) {
    if (length < capacity) bytes[length++] = (unsigned char)c; else overflow = 1;
    if (c == '\n') break;
  }
  if (ferror(stdin)) return input_error(r, "Console input failed");
  if (!length && c == EOF) return read_result(r, 0, NULL);
  if (overflow) return input_error(r, "Console input line length limit exceeded");
  if (length && bytes[length - 1] == '\n') {
    length--; if (length && bytes[length - 1] == '\r') length--;
  }
  size_t characters;
  if (!utf8_count(bytes, length, &characters)) return input_error(r, "Console input is not valid UTF-8");
  if (characters > limit) return input_error(r, "Console input line length limit exceeded");
  FValue *text = f_literal(r, bytes, length);
  return text ? read_result(r, 1, text) : NULL;
}
static FThunk *interact(FRuntime *r, FValue *io, size_t *requests, size_t line_limit) {
  if (!enter(r)) return NULL;
  FThunk *result = NULL;
  if (!io) fail(r, "missing native IO description");
  else if (io->tag == V_PURE) result = io->as.io.first;
  else if (io->tag == V_READ || io->tag == V_WRITE) {
    if (!*requests) fail(r, "native interactive request budget exhausted");
    else {
      (*requests)--;
      if (io->tag == V_READ) result = ready(r, read_line(r, line_limit));
      else {
        FValue *text = force(r, io->as.io.first);
        if (!text || text->tag != V_STRING) fail(r, "native write expects a string");
        else if ((text->as.string.length && fwrite(text->as.string.bytes, 1, text->as.string.length, stdout) != text->as.string.length) || fputc('\n', stdout) == EOF)
          fail(r, "native stdout write failed");
        else result = ready(r, f_unit(r));
      }
    }
  } else if (io->tag == V_BIND) {
    FValue *first = force(r, io->as.io.first);
    FThunk *value = first ? interact(r, first, requests, line_limit) : NULL;
    FValue *next = value ? force(r, io->as.io.second) : NULL;
    FValue *following = next ? apply_thunk(r, next, value) : NULL;
    if (following) result = interact(r, following, requests, line_limit);
  } else fail(r, "native program returned a non-IO value");
  r->depth--; return result;
}
int fibril_native_interactive_run(FEval entry, size_t requests, size_t line_characters) {
  FRuntime r = {0};
  if (line_characters > 8192 || requests > F_MAX_STEPS) fail(&r, "native interactive admission limit exceeded");
  FValue *io = r.error ? NULL : evaluate(&r, entry, NULL);
  FThunk *final = io ? interact(&r, io, &requests, line_characters) : NULL;
  FValue *unit = final ? force(&r, final) : NULL;
  if (!r.error && (!unit || unit->tag != V_UNIT)) fail(&r, "native main did not return unit");
  /* Earlier effects can be visible even when later computation fails. */
  if (!r.error && fflush(stdout) == EOF) fail(&r, "native stdout flush failed");
  int status = r.error ? 1 : 0;
  if (r.error) fprintf(stderr, "fibril native: %s\n", r.error);
  while (r.allocations) { FAllocation *next = r.allocations->next; free(r.allocations); r.allocations = next; }
  return status;
}
int fibril_native_run(FEval entry) {
  FRuntime r = {0};
  FValue *io = evaluate(&r, entry, NULL);
  FThunk *final = io ? plan(&r, io) : NULL;
  FValue *unit = final ? force(&r, final) : NULL;
  if (!r.error && (!unit || unit->tag != V_UNIT)) fail(&r, "native main did not return unit");
  if (!r.error) for (FAction *a = r.head; a; a = a->next) {
    if ((a->length && fwrite(a->bytes, 1, a->length, stdout) != a->length) || fputc('\n', stdout) == EOF) {
      fail(&r, "native stdout write failed"); break;
    }
  }
  if (!r.error && fflush(stdout) == EOF) fail(&r, "native stdout flush failed");
  int status = r.error ? 1 : 0;
  if (r.error) fprintf(stderr, "fibril native: %s\n", r.error);
  while (r.allocations) { FAllocation *next = r.allocations->next; free(r.allocations); r.allocations = next; }
  return status;
}
