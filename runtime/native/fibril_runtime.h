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
/* Tail-position helpers (f_apply, f_apply_variable, f_bool_case, f_unit_case, f_nominal_case,
   f_variant_case, f_pair_case, f_nat_case, f_rec_case, f_seq_case) may hand their continuation to
   the enclosing evaluate instead of returning a value. Generated code must therefore call them only
   as `return helper(...)` from an FEval function, and nothing may inspect their result. */
FValue *f_apply(FRuntime *r, FEnv *env, FEval function, FEval argument);
/* Checked variable arguments already name a lazy thunk. Forward that thunk
   without forcing it or changing its allocation owner. Erased calls skip lookup. */
FValue *f_apply_variable(FRuntime *r, FEnv *env, FEval function, size_t index);
FValue *f_append(FRuntime *r, FEnv *env, FEval left, FEval right);
/* Trusted literal storage must remain immutable/alive through the run. */
FValue *f_bytes_literal(FRuntime *r, const unsigned char *bytes, size_t length);
FValue *f_bytes_append(FRuntime *r, FEnv *env, FEval left, FEval right);
/* Octet-for-octet equality of two Bytes values; returns Bool. */
FValue *f_bytes_equal(FRuntime *r, FEnv *env, FEval left, FEval right);
/* Byte at a Word position as a Word, or 256 past the end; the position is not unary. */
FValue *f_bytes_word_at(FRuntime *r, FEnv *env, FEval index, FEval bytes);
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
/* Per-invocation evaluation limits for the *_limited entry points. A zero field keeps the build
   default (100000 steps, depth 512, 16 MiB; see F_MAX_* in fibril_runtime.c). Raising a limit is the
   embedder's decision. Each limit stays finite: a value above its ceiling is rejected with
   INVALID_ARGUMENT, never clamped. Lowering a limit is always safe.
   The depth ceiling is a hard bound on the setting, NOT a portable safe stack depth: accepting
   16384 does not mean 16384 nested evaluations fit. Depth is a C-stack bound (several C frames per
   unit), so what fits depends on stack size, compiler, optimization and platform. One data point:
   on an 8 MB stack at -O1, about 33000 ran and about 65000 overflowed; unoptimized builds and small
   thread stacks need much less. Keep the default 512 unless you have measured your stack. */
typedef struct { size_t steps, depth, bytes; } FNativeLimits;
#define FIBRIL_LIMIT_CEILING_STEPS ((size_t)1073741824)
#define FIBRIL_LIMIT_CEILING_DEPTH ((size_t)16384)
#define FIBRIL_LIMIT_CEILING_BYTES ((size_t)1073741824)
/* What an invocation used, reported on success and on failure: evaluation steps, peak nested
   evaluation depth, and bytes charged against the allocation budget. */
typedef struct { size_t steps, peak_depth, bytes; } FNativeUsage;
typedef struct {
  FNativeStatus status;
  /* NULL on success; otherwise immutable static storage, valid after return.
     Message wording is diagnostic, not a machine-readable error code. */
  const char *message;
  FNativeUsage usage;
} FNativeResult;
/* No stdio or process termination; each call owns and releases its arena.
   Both callbacks and entry are required. Existing fixed budgets still apply.
   Host callbacks are trusted native code, not a checked Fibril FFI. */
FNativeResult fibril_native_embed(FEval entry, const FNativeHost *host);
/* Same, with per-invocation limits (NULL keeps every default). The embedded no-heap profile
   (fibril_native_embed_arena) keeps the default evaluation limits; its allocation bound is the arena. */
FNativeResult fibril_native_embed_limited(FEval entry, const FNativeHost *host, const FNativeLimits *limits);
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
