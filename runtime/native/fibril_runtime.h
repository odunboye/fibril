/* Experimental Fibril native runtime. This API is trusted native code. */
#ifndef FIBRIL_RUNTIME_H
#define FIBRIL_RUNTIME_H
#include <stddef.h>

typedef struct FRuntime FRuntime;
typedef struct FEnv FEnv;
typedef struct FValue FValue;
typedef FValue *(*FEval)(FRuntime *, FEnv *);

FValue *f_unit(FRuntime *r);
FValue *f_erased(FRuntime *r);
FValue *f_literal(FRuntime *r, const unsigned char *bytes, size_t length);
FValue *f_variable(FRuntime *r, FEnv *env, size_t index);
FValue *f_lambda(FRuntime *r, FEnv *env, int erased, FEval body);
FValue *f_apply(FRuntime *r, FEnv *env, FEval function, FEval argument);
FValue *f_append(FRuntime *r, FEnv *env, FEval left, FEval right);
FValue *f_unit_case(FRuntime *r, FEnv *env, FEval scrutinee, FEval body);
FValue *f_pure(FRuntime *r, FEnv *env, FEval value);
FValue *f_bind(FRuntime *r, FEnv *env, FEval action, FEval continuation);
FValue *f_write(FRuntime *r, FEnv *env, FEval text);
int fibril_native_run(FEval entry);
#endif
