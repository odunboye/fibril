#ifndef FIBRIL_EXPERIMENTAL_PYTHON_BRIDGE_H
#define FIBRIL_EXPERIMENTAL_PYTHON_BRIDGE_H

#include <stddef.h>

/* Experimental C-only boundary. Not the future Fibril FFI or a stable ABI. */
typedef enum {
    FIBRIL_PY_OK = 0,
    FIBRIL_PY_NOT_READY,
    FIBRIL_PY_INVALID_ARGUMENT,
    FIBRIL_PY_EXCEPTION
} FibrilPyStatus;

/*
 * Call module.function(argument), converting its result through Python's
 * numeric double conversion. The caller owns a running main interpreter and
 * must hold its GIL. Only GIL-enabled CPython >= 3.12 is supported here.
 *
 * Names must be non-NULL, NUL-terminated UTF-8 strings; output must be valid writable
 * storage. If error != NULL and capacity > 0, it must point to that many writable
 * bytes. Error text is bounded ASCII (Unicode escaped), possibly truncated.
 * Output is changed only on success. No Python references escape the call.
 *
 * Imports/calls/conversions can execute arbitrary Python/native code. This API
 * is not a sandbox, cancellation facility, thread attachment, or proof boundary.
 */
FibrilPyStatus fibril_py_call_double(
    const char *module, const char *function, double argument,
    double *output, char *error, size_t capacity);

#endif
