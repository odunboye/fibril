# Python interoperability

Status: architecture direction. No Fibril Python backend, FFI elaboration, or
generated-C calls exist yet. Optional host-side experiments are not language support.

## Goal

Use Python's libraries without reimplementing its ecosystem. Start with explicit,
effectful interoperability, not transparent Python semantics in trusted terms.

## Two complementary bridges

| Approach | Intended use | Trade-offs |
| --- | --- | --- |
| Worker process | Initial application integration and protocol validation | Serialization/IPC overhead; isolates interpreter crashes, not a security sandbox |
| Embedded CPython | Direct calls from future generated C through a small optional adapter | Lower boundary overhead, but interpreter/native-extension crashes share the process |

Conceptual native architecture:

    Fibril -> generated C -> optional CPython adapter -> Python modules/extensions

C generation is not implemented yet. Keep interpreter-specific code in the
adapter rather than spread it across generated functions. Normal Fibril native
executables must not require Python.

## Worker progression

1. Versioned request/response protocol and validated basic values.
2. Structured Python errors, cancellation, timeouts, and process lifecycle.
3. Binary arrays, then shared memory/DLPack where justified.
4. Explicit ownership, aliasing, synchronization, and device rules for zero-copy.

A timeout on a future wait is not automatic cancellation of Python/native work.
A worker process is not a sandbox; untrusted code needs additional isolation.

## Embedded progression

1. Small C embedding experiment independent of compiler code.
2. Define interpreter ownership/lifecycle and supported CPython configurations.
3. Reference ownership, conversion failures, and exception translation tests.
4. Typed Fibril FFI/effect integration when the native backend exists.
5. Numeric arrays/opaque foreign handles only with specified lifetime rules.

Threading, free-threaded builds, subinterpreters, native extensions, and Python
version/ABI compatibility require deliberate support—not assumptions based on a
single call succeeding. Stable ABI/limited API use is a separate decision.

## Trust boundaries

- Python calls are effectful; never unfold them in trusted type normalization.
- Python type annotations are hints, not proofs.
- Validate returned values before constructing dependent guarantees.
- Never turn a Python result or exception into an arbitrary proof inhabitant.
- Native extensions can corrupt memory or crash embedded callers.
- No hard-real-time guarantees for Python calls, allocation, or interpreter locks.
- Python execution stays outside embedded deadline-critical paths.

## Dependencies and targets

Use existing virtual environments/package tools; do not implement a pip resolver.
Record interpreter and environment requirements explicitly alongside a future
Fibril manifest integration. Builds must not automatically install Python packages
or execute downloaded hooks. No exact manifest schema is committed yet.

Native/server: worker initially, optional embedding later.
Browser: remote service first; investigate Pyodide separately.
Bare metal: do not assume a Python interpreter exists.
Neither approach requires replacing the chosen C/JS backends.

## References

- [CPython embedding](https://docs.python.org/3/extending/embedding.html)
- [Initialization/configuration](https://docs.python.org/3/c-api/init_config.html)
- [Thread state and GIL](https://docs.python.org/3/c-api/init.html)
- [Reference counting](https://docs.python.org/3/c-api/refcounting.html)

These document foreign-runtime obligations, not Fibril logical soundness.
