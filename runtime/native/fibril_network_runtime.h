#ifndef FIBRIL_NETWORK_RUNTIME_H
#define FIBRIL_NETWORK_RUNTIME_H
#include "fibril_runtime.h"
/* Inert constructor used only by generated network-profile C. */
FValue *f_network(FRuntime *, FEnv *, size_t operation, FEval arguments);
int fibril_native_network_run(FEval entry);
#endif
