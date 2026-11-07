/* Experimental Fibril native runtime. This API is trusted native code. */
#ifndef FIBRIL_RUNTIME_H
#define FIBRIL_RUNTIME_H
#include <stddef.h>

typedef struct FRuntime FRuntime;
typedef struct FEnv FEnv;
typedef struct FValue FValue;
typedef FValue *(*FEval)(FRuntime *, FEnv *);

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
FValue *f_literal(FRuntime *r, const unsigned char *bytes, size_t length);
FValue *f_variable(FRuntime *r, FEnv *env, size_t index);
FValue *f_lambda(FRuntime *r, FEnv *env, int erased, FEval body);
FValue *f_apply(FRuntime *r, FEnv *env, FEval function, FEval argument);
FValue *f_append(FRuntime *r, FEnv *env, FEval left, FEval right);
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
int fibril_native_run(FEval entry);
/* Incremental execution may leave output before a later error. */
int fibril_native_interactive_run(FEval entry, size_t requests, size_t line_characters);
/* File scopes require this explicit runner; cleanup does not consume requests. */
int fibril_native_resource_run(FEval entry, size_t requests, size_t line_characters);
#endif
