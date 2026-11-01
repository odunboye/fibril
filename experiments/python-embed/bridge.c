/* CPython-specific code stays out of compiler/kernel modules.
 * API reference: docs.python.org/3/c-api/ and docs/python-interop.md.
 */
#include <Python.h>
#include <stdio.h>
#include "bridge.h"

#if PY_VERSION_HEX < 0x030C0000
#error "The experiment requires CPython 3.12 or newer."
#endif
#ifdef Py_GIL_DISABLED
#error "Free-threaded CPython is not supported by this experiment."
#endif

static void message(char *buffer, size_t capacity, const char *text) {
    if (buffer != NULL && capacity > 0) {
        (void)snprintf(buffer, capacity, "%s", text);
    }
}

/* Consume the active exception and any formatting exception. Every object here
 * is owned locally; all ordinary failure paths release their references.
 */
static void exception_message(char *buffer, size_t capacity) {
    PyObject *exception = PyErr_GetRaisedException();
    PyObject *text = exception != NULL ? PyObject_Str(exception) : NULL;
    PyObject *ascii = text != NULL
        ? PyUnicode_AsEncodedString(text, "ascii", "backslashreplace") : NULL;
    const char *detail = ascii != NULL ? PyBytes_AsString(ascii) : NULL;
    message(buffer, capacity, detail != NULL ? detail : "Python operation failed");
    Py_XDECREF(ascii);
    Py_XDECREF(text);
    Py_XDECREF(exception);
    PyErr_Clear();
}

FibrilPyStatus fibril_py_call_double(
    const char *module, const char *function, double argument,
    double *output, char *error, size_t capacity
) {
    message(error, capacity, "");
    if (module == NULL || function == NULL || output == NULL) {
        message(error, capacity, "Invalid bridge argument");
        return FIBRIL_PY_INVALID_ARGUMENT;
    }
    if (!Py_IsInitialized() || !PyGILState_Check()) {
        message(error, capacity, "Caller must own an initialized interpreter and GIL");
        return FIBRIL_PY_NOT_READY;
    }
    /* Do not consume a caller's pre-existing Python exception. */
    if (PyErr_Occurred()) {
        message(error, capacity, "Caller has a pending Python exception");
        return FIBRIL_PY_NOT_READY;
    }

    FibrilPyStatus status = FIBRIL_PY_EXCEPTION;
    PyObject *imported = NULL, *callable = NULL, *input = NULL, *result = NULL;
    imported = PyImport_ImportModule(module);
    if (imported == NULL) goto done;
    callable = PyObject_GetAttrString(imported, function);
    if (callable == NULL) goto done;
    if (!PyCallable_Check(callable)) {
        PyErr_SetString(PyExc_TypeError, "Requested Python attribute is not callable");
        goto done;
    }
    input = PyFloat_FromDouble(argument);
    if (input == NULL) goto done;
    result = PyObject_CallOneArg(callable, input);
    if (result == NULL) goto done;
    double converted = PyFloat_AsDouble(result);
    if (PyErr_Occurred()) goto done;
    *output = converted;
    status = FIBRIL_PY_OK;

done:
    if (status != FIBRIL_PY_OK) exception_message(error, capacity);
    Py_XDECREF(result);
    Py_XDECREF(input);
    Py_XDECREF(callable);
    Py_XDECREF(imported);
    return status;
}
