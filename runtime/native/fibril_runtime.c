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
typedef struct FInput { size_t identity, generation; FILE *file; const char *close_error; struct FInput *next; } FInput;
struct FRuntime { FAllocation *allocations; size_t bytes, steps, depth, actions; const char *error; FAction *head, *tail; FInput *inputs; size_t next_input; };
struct FEnv { FThunk *value; FEnv *tail; };
typedef enum { V_UNIT, V_ERASED, V_BOOL, V_STRING, V_BYTES, V_CLOSURE, V_NOMINAL, V_VARIANT,
               V_NAT_ZERO, V_NAT_SUCC, V_REC_END, V_REC_MORE, V_SEQ_NIL, V_SEQ_CONS,
               V_PURE, V_BIND, V_WRITE, V_READ, V_PAIR, V_INPUT_HANDLE,
               V_WITH_INPUT, V_READ_INPUT, V_READ_BYTES, V_WRITE_BYTES, V_FLUSH_BYTES } FTag;
typedef enum { F_NAT, F_NAT_RUNTIME, F_REC, F_SEQ } FFoldKind;
struct FValue {
  FTag tag;
  union {
    struct { const unsigned char *bytes; size_t length; } string;
    struct { const unsigned char *data; size_t length; } bytes;
    int boolean;
    FThunk *nominal;
    struct { size_t tag; FThunk *payload; } variant;
    struct { FThunk *head, *tail; } recursive;
    struct { FEval body; FEnv *env; int erased; } closure;
    struct { FThunk *first, *second; } io;
    struct { FThunk *first, *second; } pair;
    struct { size_t identity, generation; } handle;
  } as;
};
struct FThunk {
  FEval code;
  FEnv *env;
  FValue *value;
  int state, is_fold;
  FFoldKind fold_kind;
  FThunk *input;
  FEval base, step;
};

static FValue *evaluate_fold(FRuntime *r, FFoldKind kind, FEnv *env,
                             FEval base, FEval step, FThunk *input);

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
  if (t) { memset(t, 0, sizeof(*t)); t->code = code; t->env = env; }
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
  FValue *value = t->is_fold ? evaluate_fold(r, t->fold_kind, t->env, t->base, t->step, t->input)
                             : evaluate(r, t->code, t->env);
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
FValue *f_bytes_literal(FRuntime *r, const unsigned char *bytes, size_t length) {
  if ((length && !bytes) || length > F_MAX_BYTES) {
    fail(r, "invalid native byte literal"); return NULL;
  }
  FValue *value = new_value(r, V_BYTES);
  if (value) { value->as.bytes.data = bytes; value->as.bytes.length = length; }
  return value;
}
FValue *f_bytes_append(FRuntime *r, FEnv *env, FEval left, FEval right) {
  if (!left || !right) { fail(r, "missing native byte append operand"); return NULL; }
  FValue *a = evaluate(r, left, env);
  FValue *b = a ? evaluate(r, right, env) : NULL;
  if (!a || !b || a->tag != V_BYTES || b->tag != V_BYTES) {
    fail(r, "native byte append expects Bytes"); return NULL;
  }
  if (a->as.bytes.length > SIZE_MAX - b->as.bytes.length) {
    fail(r, "native byte length overflow"); return NULL;
  }
  size_t length = a->as.bytes.length + b->as.bytes.length;
  unsigned char *data = allocate(r, length ? length : 1);
  if (!data) return NULL;
  if (a->as.bytes.length) memcpy(data, a->as.bytes.data, a->as.bytes.length);
  if (b->as.bytes.length) memcpy(data + a->as.bytes.length, b->as.bytes.data, b->as.bytes.length);
  return f_bytes_literal(r, data, length);
}
/* Charge even memoized natural traversals, which otherwise could cycle forever
   in a malformed trusted fixture. Arena allocation has its separate bound. */
static int byte_work(FRuntime *r) {
  if (!enter(r)) return 0;
  r->depth--; return 1;
}
static FValue *byte_natural(FRuntime *r, size_t count) {
  FValue *result = f_nat_zero(r);
  for (size_t n = 0; result && n < count; n++) {
    if (!byte_work(r)) return NULL;
    FThunk *tail = ready(r, result);
    if (!tail) return NULL;
    result = new_value(r, V_NAT_SUCC);
    if (result) result->as.recursive.tail = tail;
  }
  return result;
}
FValue *f_bytes_length(FRuntime *r, FEnv *env, FEval expression) {
  if (!expression) { fail(r, "missing native byte length operand"); return NULL; }
  FValue *bytes = evaluate(r, expression, env);
  if (!bytes || bytes->tag != V_BYTES) { fail(r, "native byte length expects Bytes"); return NULL; }
  return byte_natural(r, bytes->as.bytes.length);
}
/* Saturate instead of wrapping. Still validate/charge every successor tail. */
static int byte_position(FRuntime *r, FEnv *env, FEval expression, size_t *position) {
  if (!expression) { fail(r, "missing native byte position"); return 0; }
  FValue *value = evaluate(r, expression, env);
  size_t n = 0;
  while (value && value->tag == V_NAT_SUCC) {
    if (!byte_work(r)) return 0;
    if (n < SIZE_MAX) n++;
    value = force(r, value->as.recursive.tail);
  }
  if (!value || value->tag != V_NAT_ZERO) { fail(r, "native byte position expects Nat"); return 0; }
  *position = n; return 1;
}
FValue *f_bytes_index(FRuntime *r, FEnv *env, FEval index, FEval expression) {
  if (!expression) { fail(r, "missing native byte index operand"); return NULL; }
  size_t offset;
  if (!byte_position(r, env, index, &offset)) return NULL;
  FValue *bytes = evaluate(r, expression, env);
  if (!bytes || bytes->tag != V_BYTES) { fail(r, "native byte index expects Bytes"); return NULL; }
  FValue *result = new_value(r, V_VARIANT);
  if (!result) return NULL;
  if (offset < bytes->as.bytes.length) {
    result->as.variant.tag = 1;
    result->as.variant.payload = ready(r, byte_natural(r, bytes->as.bytes.data[offset]));
    if (!result->as.variant.payload) return NULL;
  }
  return result;
}
FValue *f_bytes_slice(FRuntime *r, FEnv *env, FEval start, FEval count, FEval expression) {
  if (!expression) { fail(r, "missing native byte slice operand"); return NULL; }
  size_t offset, length;
  if (!byte_position(r, env, start, &offset) || !byte_position(r, env, count, &length)) return NULL;
  FValue *bytes = evaluate(r, expression, env);
  if (!bytes || bytes->tag != V_BYTES) { fail(r, "native byte slice expects Bytes"); return NULL; }
  if (offset > bytes->as.bytes.length) offset = bytes->as.bytes.length;
  size_t remaining = bytes->as.bytes.length - offset;
  if (length > remaining) length = remaining;
  /* Views are immutable; their arena/static storage lives through the run. */
  const unsigned char *data = length ? bytes->as.bytes.data + offset : NULL;
  return f_bytes_literal(r, data, length);
}
FValue *f_bytes_octet(FRuntime *r, FEnv *env, FEval expression) {
  if (!expression) { fail(r, "missing native byte octet operand"); return NULL; }
  FValue *value = evaluate(r, expression, env);
  unsigned char octet = 0;
  while (value && value->tag == V_NAT_SUCC) {
    if (!byte_work(r)) return NULL;
    octet = (unsigned char)(octet + 1u);
    value = force(r, value->as.recursive.tail);
  }
  if (!value || value->tag != V_NAT_ZERO) { fail(r, "native byte octet expects Nat"); return NULL; }
  unsigned char *data = allocate(r, 1);
  if (!data) return NULL;
  *data = octet;
  return f_bytes_literal(r, data, 1);
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
static FThunk *fold_thunk(FRuntime *r, FFoldKind kind, FEnv *env,
                          FEval base, FEval step, FThunk *input) {
  FThunk *result = thunk(r, NULL, env);
  if (result) { result->is_fold = 1; result->fold_kind = kind; result->base = base; result->step = step; result->input = input; }
  return result;
}
static FValue *evaluate_fold(FRuntime *r, FFoldKind kind, FEnv *env,
                             FEval base, FEval step, FThunk *input) {
  if (!enter(r)) return NULL;
  FValue *result = NULL;
  FValue *value = force(r, input);
  if (value) {
    int is_base = (kind == F_NAT || kind == F_NAT_RUNTIME) ? value->tag == V_NAT_ZERO :
                  kind == F_REC ? value->tag == V_REC_END : value->tag == V_SEQ_NIL;
    int is_step = (kind == F_NAT || kind == F_NAT_RUNTIME) ? value->tag == V_NAT_SUCC :
                  kind == F_REC ? value->tag == V_REC_MORE : value->tag == V_SEQ_CONS;
    if (is_base) result = evaluate(r, base, env);
    else if (is_step && value->as.recursive.tail && (kind != F_SEQ || value->as.recursive.head)) {
      FValue *branch = evaluate(r, step, env);
      FThunk *next = branch ? fold_thunk(r, kind, env, base, step, value->as.recursive.tail) : NULL;
      if (next && kind == F_SEQ) branch = apply_thunk(r, branch, value->as.recursive.head);
      if (next && branch) branch = apply_thunk(r, branch, kind == F_NAT_RUNTIME ? value->as.recursive.tail : NULL);
      if (next && branch) result = apply_thunk(r, branch, next);
    } else fail(r, "native fold expects a matching recursive value");
  }
  r->depth--;
  return result;
}
static FValue *fold(FRuntime *r, FFoldKind kind, FEnv *env, FEval base, FEval step, FEval value) {
  if (!base || !step || !value) { fail(r, "missing native fold expression"); return NULL; }
  FThunk *input = thunk(r, value, env);
  return input ? evaluate_fold(r, kind, env, base, step, input) : NULL;
}
FValue *f_nat_rec(FRuntime *r, FEnv *env, FEval base, FEval step, FEval value) { return fold(r, F_NAT, env, base, step, value); }
FValue *f_nat_rec_runtime(FRuntime *r, FEnv *env, FEval base, FEval step, FEval value) { return fold(r, F_NAT_RUNTIME, env, base, step, value); }
FValue *f_rec_fold(FRuntime *r, FEnv *env, FEval base, FEval step, FEval value) { return fold(r, F_REC, env, base, step, value); }
FValue *f_seq_fold(FRuntime *r, FEnv *env, FEval base, FEval step, FEval value) { return fold(r, F_SEQ, env, base, step, value); }

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
FValue *f_nat_zero(FRuntime *r) { return new_value(r, V_NAT_ZERO); }
FValue *f_rec_end(FRuntime *r) { return new_value(r, V_REC_END); }
FValue *f_seq_nil(FRuntime *r) { return new_value(r, V_SEQ_NIL); }
static FValue *recursive_value(FRuntime *r, FEnv *env, FTag tag, FEval head, FEval tail) {
  if (!tail || (tag == V_SEQ_CONS && !head)) { fail(r, "missing native recursive field"); return NULL; }
  FValue *value = new_value(r, tag);
  if (!value) return NULL;
  value->as.recursive.tail = thunk(r, tail, env);
  if (!value->as.recursive.tail) return NULL;
  if (head) {
    value->as.recursive.head = thunk(r, head, env);
    if (!value->as.recursive.head) return NULL;
  }
  return value;
}
FValue *f_nat_succ(FRuntime *r, FEnv *env, FEval tail) { return recursive_value(r, env, V_NAT_SUCC, NULL, tail); }
FValue *f_rec_more(FRuntime *r, FEnv *env, FEval tail) { return recursive_value(r, env, V_REC_MORE, NULL, tail); }
FValue *f_seq_cons(FRuntime *r, FEnv *env, FEval head, FEval tail) { return recursive_value(r, env, V_SEQ_CONS, head, tail); }
FValue *f_rec_case(FRuntime *r, FEnv *env, FEval scrutinee, FEval base, FEval more) {
  if (!scrutinee || !base || !more) { fail(r, "missing native recursive-case expression"); return NULL; }
  FValue *value = evaluate(r, scrutinee, env);
  if (!value) return NULL;
  if (value->tag == V_REC_END) return evaluate(r, base, env);
  if (value->tag != V_REC_MORE || !value->as.recursive.tail) {
    fail(r, "native recursive case expects a recursive value"); return NULL;
  }
  FValue *branch = evaluate(r, more, env);
  return branch ? apply_thunk(r, branch, value->as.recursive.tail) : NULL;
}
FValue *f_seq_case(FRuntime *r, FEnv *env, FEval scrutinee, FEval base, FEval cons) {
  if (!scrutinee || !base || !cons) { fail(r, "missing native sequence-case expression"); return NULL; }
  FValue *value = evaluate(r, scrutinee, env);
  if (!value) return NULL;
  if (value->tag == V_SEQ_NIL) return evaluate(r, base, env);
  if (value->tag != V_SEQ_CONS || !value->as.recursive.head || !value->as.recursive.tail) {
    fail(r, "native sequence case expects a sequence value"); return NULL;
  }
  FValue *branch = evaluate(r, cons, env);
  branch = branch ? apply_thunk(r, branch, value->as.recursive.head) : NULL;
  return branch ? apply_thunk(r, branch, value->as.recursive.tail) : NULL;
}
FValue *f_unit_case(FRuntime *r, FEnv *env, FEval scrutinee, FEval body) {
  FValue *value = evaluate(r, scrutinee, env);
  if (!value || value->tag != V_UNIT) { fail(r, "native unit case expects unit"); return NULL; }
  return evaluate(r, body, env);
}
FValue *f_pair(FRuntime *r, FEnv *env, int first_erased, int second_erased, FEval first, FEval second) {
  FValue *v = new_value(r, V_PAIR);
  if (!v) return NULL;
  v->as.pair.first = first_erased ? NULL : thunk(r, first, env);
  v->as.pair.second = second_erased ? NULL : thunk(r, second, env);
  if ((!first_erased && !v->as.pair.first) || (!second_erased && !v->as.pair.second)) return NULL;
  return v;
}
FValue *f_pair_case(FRuntime *r, FEnv *env, FEval scrutinee, FEval branch) {
  FValue *value = evaluate(r, scrutinee, env);
  if (!value || value->tag != V_PAIR) { fail(r, "native pair case expects a pair"); return NULL; }
  FValue *first = evaluate(r, branch, env);
  FValue *second = first ? apply_thunk(r, first, value->as.pair.first) : NULL;
  return second ? apply_thunk(r, second, value->as.pair.second) : NULL;
}
static FValue *owned_pair(FRuntime *r, FValue *first, FValue *second) {
  if (!first || !second) return NULL;
  FValue *v = new_value(r, V_PAIR);
  if (!v) return NULL;
  v->as.pair.first = ready(r, first); v->as.pair.second = ready(r, second);
  return v->as.pair.first && v->as.pair.second ? v : NULL;
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
FValue *f_read_bytes(FRuntime *r, FEnv *env, FEval capacity) {
  if (!capacity) { fail(r, "missing native binary capacity"); return NULL; }
  return io1(r, env, V_READ_BYTES, capacity, NULL);
}
FValue *f_write_bytes(FRuntime *r, FEnv *env, FEval bytes) {
  if (!bytes) { fail(r, "missing native binary bytes"); return NULL; }
  return io1(r, env, V_WRITE_BYTES, bytes, NULL);
}
FValue *f_flush_bytes(FRuntime *r) { return new_value(r, V_FLUSH_BYTES); }
FValue *f_with_input(FRuntime *r, FEnv *env, FEval path, FEval body) { return io1(r, env, V_WITH_INPUT, path, body); }
FValue *f_read_input(FRuntime *r, FEnv *env, FEval handle) { return io1(r, env, V_READ_INPUT, handle, NULL); }

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
static FValue *convert_utf8(FRuntime *r, FEnv *env, FEval expression, int encode) {
  if (!expression) { fail(r, "missing native UTF8 operand"); return NULL; }
  FValue *input = evaluate(r, expression, env);
  if (!input || input->tag != (encode ? V_STRING : V_BYTES)) {
    fail(r, "native UTF8 conversion operand type mismatch"); return NULL;
  }
  const unsigned char *data = encode ? input->as.string.bytes : input->as.bytes.data;
  size_t length = encode ? input->as.string.length : input->as.bytes.length;
  if ((length && !data) || length > F_MAX_BYTES) { fail(r, "invalid native UTF8 payload or byte budget"); return NULL; }
  /* Reserve validation work even for malformed sequences; no refund on an
     early error. This is evaluator work, not the binary transport quota. */
  if (r->steps > F_MAX_STEPS || length > F_MAX_STEPS - r->steps) {
    fail(r, "native UTF8 evaluation budget exhausted"); return NULL;
  }
  r->steps += length;
  /* Existing String consumers expect addressable storage even when empty. */
  static const unsigned char empty[] = {0};
  if (!data) data = empty;
  size_t characters;
  if (!utf8_count(data, length, &characters)) return read_result(r, 0, NULL);
  FValue *payload = encode ? f_bytes_literal(r, data, length) : f_literal(r, data, length);
  return payload ? read_result(r, 1, payload) : NULL;
}
FValue *f_utf8_encode(FRuntime *r, FEnv *env, FEval expression) { return convert_utf8(r, env, expression, 1); }
FValue *f_utf8_decode(FRuntime *r, FEnv *env, FEval expression) { return convert_utf8(r, env, expression, 0); }
static FValue *input_error(FRuntime *r, const char *message) {
  FValue *text = f_literal(r, (const unsigned char *)message, strlen(message));
  return text ? read_result(r, 2, text) : NULL;
}
static FValue *read_line_from(FRuntime *r, FILE *input, size_t limit, int file_input) {
  /* Admission caps limit at 8192, so this multiplication cannot overflow. */
  size_t capacity = limit * 4 + 2, length = 0; int overflow = 0, c;
  unsigned char *bytes = allocate(r, capacity);
  if (!bytes) return NULL;
  while ((c = fgetc(input)) != EOF) {
    if (length < capacity) bytes[length++] = (unsigned char)c; else overflow = 1;
    if (c == '\n') break;
  }
  if (ferror(input)) return input_error(r, file_input ? "File read failed: Console input failed" : "Console input failed");
  if (!length && c == EOF) return read_result(r, 0, NULL);
  if (overflow) return input_error(r, file_input ? "File read failed: Console input line length limit exceeded" : "Console input line length limit exceeded");
  if (length && bytes[length - 1] == '\n') {
    length--; if (length && bytes[length - 1] == '\r') length--;
  }
  if (length && memchr(bytes, 0, length)) return input_error(r, file_input ? "File read failed: Console input contains NUL" : "Console input contains NUL");
  size_t characters;
  if (!utf8_count(bytes, length, &characters)) return input_error(r, file_input ? "File read failed: Console input is not valid UTF-8" : "Console input is not valid UTF-8");
  if (characters > limit) return input_error(r, file_input ? "File read failed: Console input line length limit exceeded" : "Console input line length limit exceeded");
  FValue *text = f_literal(r, bytes, length);
  return text ? read_result(r, 1, text) : NULL;
}
static FValue *read_line(FRuntime *r, size_t limit) {
  if (fflush(stdout) == EOF) return input_error(r, "Console stdout flush failed");
  return read_line_from(r, stdin, limit, 0);
}
static FThunk *interact(FRuntime *r, FValue *io, size_t *requests, size_t line_limit, int resources);

/* Revoke before fclose, and remember failure without retrying a descriptor
   which may already have been released/reused. This works even after r->error. */
static const char *close_input(FInput *input) {
  if (input->file) {
    FILE *file = input->file; input->file = NULL;
    if (fclose(file) != 0) input->close_error = "File close failed";
  }
  return input->close_error;
}
static FValue *input_handle(FRuntime *r, size_t identity, size_t generation) {
  FValue *value = new_value(r, V_INPUT_HANDLE);
  if (value) { value->as.handle.identity = identity; value->as.handle.generation = generation; }
  return value;
}
static FValue *read_owned_input(FRuntime *r, FValue *io, size_t line_limit) {
  FValue *handle = force(r, io->as.io.first);
  if (!handle || handle->tag != V_INPUT_HANDLE) { fail(r, "native file read expects ownership"); return NULL; }
  FInput *input = r->inputs;
  while (input && input->identity != handle->as.handle.identity) input = input->next;
  if (!input) { fail(r, "Unknown input reference"); return NULL; }
  if (!input->file) { fail(r, "Revoked input reference"); return NULL; }
  if (input->generation != handle->as.handle.generation) { fail(r, "Stale input reference"); return NULL; }
  if (input->generation == SIZE_MAX) { fail(r, "native input generation exhausted"); return NULL; }
  input->generation++;
  FValue *response = read_line_from(r, input->file, line_limit, 1);
  FValue *successor = response ? input_handle(r, input->identity, input->generation) : NULL;
  return owned_pair(r, successor, response);
}
static FValue *input_scope(FRuntime *r, FValue *io, size_t *requests, size_t line_limit) {
  FValue *path = force(r, io->as.io.first);
  if (!path || path->tag != V_STRING) { fail(r, "native file path expects String"); return NULL; }
  if (memchr(path->as.string.bytes, 0, path->as.string.length)) {
    const char *message = "File open failed: NUL in path";
    return read_result(r, 0, f_literal(r, (const unsigned char *)message, strlen(message)));
  }
  if (path->as.string.length == SIZE_MAX) { fail(r, "native path length overflow"); return NULL; }
  char *name = allocate(r, path->as.string.length + 1);
  FInput *input = allocate(r, sizeof(*input));
  if (!name || !input) return NULL;
  memcpy(name, path->as.string.bytes, path->as.string.length); name[path->as.string.length] = 0;
  memset(input, 0, sizeof(*input));
  input->file = fopen(name, "rb");
  if (!input->file) {
    const char *message = "File open failed: unable to open input";
    return read_result(r, 0, f_literal(r, (const unsigned char *)message, strlen(message)));
  }
  input->identity = r->next_input++;
  input->next = r->inputs; r->inputs = input;
  FValue *body = force(r, io->as.io.second);
  /* The region parameter is erased. Source checking forbids its runtime use. */
  FValue *at_region = body ? apply_thunk(r, body, NULL) : NULL;
  FValue *handle = at_region ? input_handle(r, input->identity, 0) : NULL;
  FValue *action = handle ? apply_thunk(r, at_region, ready(r, handle)) : NULL;
  FThunk *returned = action ? interact(r, action, requests, line_limit, 1) : NULL;
  FValue *pair = returned ? force(r, returned) : NULL;
  FValue *payload = NULL;
  if (!r->error) {
    if (!pair || pair->tag != V_PAIR) fail(r, "native scope did not return an ownership pair");
    else {
      FValue *owner = force(r, pair->as.pair.first);
      if (!owner || owner->tag != V_INPUT_HANDLE || owner->as.handle.identity != input->identity ||
          owner->as.handle.generation != input->generation || !input->file)
        fail(r, "native scope did not return current ownership");
      else {
        payload = force(r, pair->as.pair.second);
        if (!payload && !r->error) fail(r, "native scope returned no result");
      }
    }
  }
  const char *cleanup = close_input(input);
  if (r->error) return NULL;
  if (cleanup) {
    FValue *message = f_literal(r, (const unsigned char *)cleanup, strlen(cleanup));
    return read_result(r, 2, owned_pair(r, payload, message));
  }
  return read_result(r, 1, payload);
}
static FThunk *interact(FRuntime *r, FValue *io, size_t *requests, size_t line_limit, int resources) {
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
        else if (text->as.string.length && memchr(text->as.string.bytes, 0, text->as.string.length)) fail(r, "Console output contains NUL");
        else if ((text->as.string.length && fwrite(text->as.string.bytes, 1, text->as.string.length, stdout) != text->as.string.length) || fputc('\n', stdout) == EOF)
          fail(r, "native stdout write failed");
        else result = ready(r, f_unit(r));
      }
    }
  } else if (io->tag == V_WITH_INPUT || io->tag == V_READ_INPUT) {
    if (!resources) fail(r, "native resource IO requires the resource runner");
    else if (!*requests) fail(r, "native interactive request budget exhausted");
    else {
      (*requests)--;
      result = ready(r, io->tag == V_WITH_INPUT ? input_scope(r, io, requests, line_limit) : read_owned_input(r, io, line_limit));
    }
  } else if (io->tag == V_BIND) {
    FValue *first = force(r, io->as.io.first);
    FThunk *value = first ? interact(r, first, requests, line_limit, resources) : NULL;
    FValue *next = value ? force(r, io->as.io.second) : NULL;
    FValue *following = next ? apply_thunk(r, next, value) : NULL;
    if (following) result = interact(r, following, requests, line_limit, resources);
  } else fail(r, "native program returned a non-IO value");
  r->depth--; return result;
}
int fibril_native_interactive_run(FEval entry, size_t requests, size_t line_characters) {
  FRuntime r = {0};
  if (line_characters > 8192 || requests > F_MAX_STEPS) fail(&r, "native interactive admission limit exceeded");
  FValue *io = r.error ? NULL : evaluate(&r, entry, NULL);
  FThunk *final = io ? interact(&r, io, &requests, line_characters, 0) : NULL;
  FValue *unit = final ? force(&r, final) : NULL;
  if (!r.error && (!unit || unit->tag != V_UNIT)) fail(&r, "native main did not return unit");
  /* Earlier effects can be visible even when later computation fails. */
  if (!r.error && fflush(stdout) == EOF) fail(&r, "native stdout flush failed");
  int status = r.error ? 1 : 0;
  if (r.error) fprintf(stderr, "fibril native: %s\n", r.error);
  while (r.allocations) { FAllocation *next = r.allocations->next; free(r.allocations); r.allocations = next; }
  return status;
}
int fibril_native_resource_run(FEval entry, size_t requests, size_t line_characters) {
  FRuntime r = {0};
  if (line_characters > 8192 || requests > F_MAX_STEPS) fail(&r, "native resource admission limit exceeded");
  FValue *io = r.error ? NULL : evaluate(&r, entry, NULL);
  FThunk *final = io ? interact(&r, io, &requests, line_characters, 1) : NULL;
  FValue *unit = final ? force(&r, final) : NULL;
  if (!r.error && (!unit || unit->tag != V_UNIT)) fail(&r, "native main did not return unit");
  if (!r.error && fflush(stdout) == EOF) fail(&r, "native stdout flush failed");
  /* A nonallocating backstop closes every registered file even on evaluator,
     request or allocation failure. Closed entries retain their close status. */
  int cleanup_failed = 0;
  for (FInput *input = r.inputs; input; input = input->next) {
    if (close_input(input)) cleanup_failed = 1;
  }
  int status = r.error || cleanup_failed ? 1 : 0;
  if (r.error) fprintf(stderr, "fibril native: %s\n", r.error);
  for (FInput *input = r.inputs; input; input = input->next)
    if (input->close_error) fprintf(stderr, "fibril native cleanup: %s\n", input->close_error);
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
    if (a->length && memchr(a->bytes, 0, a->length)) { fail(&r, "Console output contains NUL"); break; }
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
