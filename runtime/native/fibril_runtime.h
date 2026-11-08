/* Experimental Fibril native runtime. This API is trusted native code. */
#ifndef FIBRIL_RUNTIME_H
#define FIBRIL_RUNTIME_H
#include <stddef.h>
#include <stdint.h>

typedef struct FRuntime FRuntime;
typedef struct FEnv FEnv;
typedef struct FValue FValue;
typedef FValue *(*FEval)(FRuntime *, FEnv *);

/* Enter a checked closed global under the ordinary step/depth budget. */
FValue *f_global(FRuntime *r, FEval body);
FValue *f_unit(FRuntime *r);
FValue *f_bool(FRuntime *r, int value);
FValue *f_bool_case(FRuntime *r, FEnv *env, FEval scrutinee, FEval yes, FEval no);
FValue *f_string_equal(FRuntime *r, FEnv *env, FEval left, FEval right);
FValue *f_nominal(FRuntime *r, FEnv *env, FEval value);
FValue *f_nominal_case(FRuntime *r, FEnv *env, FEval scrutinee, FEval branch);
FValue *f_variant(FRuntime *r, FEnv *env, size_t tag, FEval payload);
FValue *f_variant_case(FRuntime *r, FEnv *env, FEval scrutinee, size_t count, const FEval *branches);
FValue *f_nat_zero(FRuntime *r);
FValue *f_nat_succ(FRuntime *r, FEnv *env, FEval tail);
FValue *f_rec_end(FRuntime *r);
FValue *f_rec_more(FRuntime *r, FEnv *env, FEval tail);
FValue *f_seq_nil(FRuntime *r);
FValue *f_seq_cons(FRuntime *r, FEnv *env, FEval head, FEval tail);
FValue *f_nat_case(FRuntime *r, FEnv *env, FEval value, FEval base, FEval more);
FValue *f_rec_case(FRuntime *r, FEnv *env, FEval value, FEval base, FEval more);
FValue *f_seq_case(FRuntime *r, FEnv *env, FEval value, FEval base, FEval cons);
FValue *f_nat_rec(FRuntime *r, FEnv *env, FEval base, FEval step, FEval value);
FValue *f_nat_rec_runtime(FRuntime *r, FEnv *env, FEval base, FEval step, FEval value);
FValue *f_rec_fold(FRuntime *r, FEnv *env, FEval base, FEval step, FEval value);
FValue *f_seq_fold(FRuntime *r, FEnv *env, FEval base, FEval step, FEval value);
FValue *f_erased(FRuntime *r);
/* Unsigned 64-bit Word: arithmetic wraps modulo 2^64, comparisons are unsigned. */
FValue *f_word(FRuntime *r, uint64_t value);
/* Decimal digits, no sign or padding; the result is an ordinary String. */
FValue *f_word_to_string(FRuntime *r, FEnv *env, FEval value);
/* Division returns a variant: tag 0 divide-by-zero (no payload), tag 1 the Word result. */
FValue *f_word_div(FRuntime *r, FEnv *env, FEval left, FEval right);
FValue *f_word_rem(FRuntime *r, FEnv *env, FEval left, FEval right);
/* Counts a canonical Nat chain modulo 2^64; each successor is charged to the step budget. */
FValue *f_word_from_nat(FRuntime *r, FEnv *env, FEval value);
FValue *f_word_add(FRuntime *r, FEnv *env, FEval left, FEval right);
FValue *f_word_sub(FRuntime *r, FEnv *env, FEval left, FEval right);
FValue *f_word_mul(FRuntime *r, FEnv *env, FEval left, FEval right);
FValue *f_word_eq(FRuntime *r, FEnv *env, FEval left, FEval right);
FValue *f_word_lt(FRuntime *r, FEnv *env, FEval left, FEval right);
/* Evaluate body in a sub-arena; first-order data is copied out, then the arena is freed. */
FValue *f_with_region(FRuntime *r, FEnv *env, FEval body);
FValue *f_literal(FRuntime *r, const unsigned char *bytes, size_t length);
FValue *f_variable(FRuntime *r, FEnv *env, size_t index);
FValue *f_lambda(FRuntime *r, FEnv *env, int erased, FEval body);
/* Recursive function: body sees the function itself as variable 0. Termination is the
   checker's size-change admission; the runtime only ties the knot. */
FValue *f_fix(FRuntime *r, FEnv *env, FEval body);
FValue *f_apply(FRuntime *r, FEnv *env, FEval function, FEval argument);
/* Checked variable arguments already name a lazy thunk. Forward that thunk
   without forcing it or changing its allocation owner. Erased calls skip lookup. */
FValue *f_apply_variable(FRuntime *r, FEnv *env, FEval function, size_t index);
FValue *f_append(FRuntime *r, FEnv *env, FEval left, FEval right);
/* Trusted literal storage must remain immutable/alive through the run. */
FValue *f_bytes_literal(FRuntime *r, const unsigned char *bytes, size_t length);
FValue *f_bytes_append(FRuntime *r, FEnv *env, FEval left, FEval right);
FValue *f_bytes_length(FRuntime *r, FEnv *env, FEval value);
FValue *f_utf8_encode(FRuntime *r, FEnv *env, FEval value);
FValue *f_utf8_decode(FRuntime *r, FEnv *env, FEval value);
FValue *f_bytes_octet(FRuntime *r, FEnv *env, FEval value);
FValue *f_bytes_length_is(FRuntime *, FEnv *, FEval, FEval);
FValue *f_bytes_index(FRuntime *r, FEnv *env, FEval index, FEval bytes);
FValue *f_bytes_slice(FRuntime *r, FEnv *env, FEval start, FEval count, FEval bytes);
FValue *f_unit_case(FRuntime *r, FEnv *env, FEval scrutinee, FEval body);
FValue *f_pair(FRuntime *r, FEnv *env, int first_erased, int second_erased, FEval first, FEval second);
FValue *f_pair_case(FRuntime *r, FEnv *env, FEval scrutinee, FEval branch);
/* Trusted backend operations; no source constructors for live references. */
FValue *f_with_input(FRuntime *r, FEnv *env, FEval path, FEval body);
FValue *f_read_input(FRuntime *r, FEnv *env, FEval handle);
FValue *f_pure(FRuntime *r, FEnv *env, FEval value);
FValue *f_bind(FRuntime *r, FEnv *env, FEval action, FEval continuation);
FValue *f_write(FRuntime *r, FEnv *env, FEval text);
/* Inert request; only the separate interactive runner may execute it. */
FValue *f_read_line(FRuntime *r);
FValue *f_read_bytes(FRuntime *r, FEnv *env, FEval capacity);
FValue *f_write_bytes(FRuntime *r, FEnv *env, FEval bytes);
FValue *f_flush_bytes(FRuntime *r);
FValue *f_reject_bytes(FRuntime *r);
/* Inert binary-only iteration; S/R erased. Tags 0 Done/Finished, 1 Continue/
   Exhausted each require one payload. Not a trusted-fixture type proof. */
FValue *f_iterate_binary(FRuntime *, FEnv *, FEval count, FEval step, FEval initial);
/* Link fibril_binary_runtime.c instead of fibril_runtime.c for this runner. */
int fibril_native_binary_run(FEval entry, size_t requests, size_t capacity);
/* Experimental embedding boundary for staged console IO only. Callbacks return
   zero on success, nonzero on failure. Bytes are borrowed for the callback only;
   writes may be split (including a separate newline). No callback is called
   until evaluation and text validation succeed. Host effects are not rolled
   back on callback failure. Callbacks must return normally; no longjmp across
   the runtime. No runtime/value pointer escapes this synchronous invocation. */
typedef int (*FNativeWrite)(void *context, const unsigned char *bytes, size_t length);
typedef int (*FNativeFlush)(void *context);
typedef struct {
  void *context;
  FNativeWrite write;
  FNativeFlush flush;
} FNativeHost;
typedef enum {
  F_NATIVE_OK = 0,
  F_NATIVE_INVALID_ARGUMENT,
  F_NATIVE_PROGRAM_ERROR,
  F_NATIVE_WRITE_ERROR,
  F_NATIVE_FLUSH_ERROR
} FNativeStatus;
typedef struct {
  FNativeStatus status;
  /* NULL on success; otherwise immutable static storage, valid after return.
     Message wording is diagnostic, not a machine-readable error code. */
  const char *message;
} FNativeResult;
/* No stdio or process termination; each call owns and releases its arena.
   Both callbacks and entry are required. Existing fixed budgets still apply.
   Host callbacks are trusted native code, not a checked Fibril FFI. */
FNativeResult fibril_native_embed(FEval entry, const FNativeHost *host);
/* Supplied by newly emitted `emit-c` console programs, NOT the runtime itself.
   Compile generated C with -DFIBRIL_EMBED_ONLY to omit its standalone main.
   One generated program per linked image; other emission modes do not expose it. */
FNativeResult fibril_program_embed(const FNativeHost *host);
int fibril_native_run(FEval entry);
/* Incremental execution may leave output before a later error. */
int fibril_native_interactive_run(FEval entry, size_t requests, size_t line_characters);
/* File scopes require this explicit runner; cleanup does not consume requests. */
int fibril_native_resource_run(FEval entry, size_t requests, size_t line_characters);
#endif
