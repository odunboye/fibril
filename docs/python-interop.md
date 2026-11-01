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

## Optional C-only experiment

The isolated prototype in experiments/python-embed demonstrates direct C calls
to the Python standard library. It does not require or implement a Fibril backend.

```sh
make python-embed-test
```

Prerequisites: a C compiler, GIL-enabled CPython >= 3.12 development files, and
matching python3-config. Override PYTHON_CONFIG or CC explicitly if needed.
No dependencies are installed. This target is intentionally outside make test
and ordinary compiler builds.

- [bridge.h](../experiments/python-embed/bridge.h): small unary-double call API.
- [bridge.c](../experiments/python-embed/bridge.c): imports, invocation, reference
  cleanup, numeric conversion, and bounded ASCII-escaped exception messages.
- [test_bridge.c](../experiments/python-embed/test_bridge.c): isolated interpreter
  initialization, success/failure, unchanged outputs on errors, pending exceptions,
  GIL requirements, small buffers, and repeated cleanup paths.

The host owns initialization/finalization and must call from the main interpreter
while holding its GIL. Free-threaded builds are rejected at compilation; subinterpreters,
concurrent finalization, interpreter attachment, and cancellation are unsupported.
The adapter neither creates an interpreter nor attaches threads.

The experiment was built/tested here with CPython 3.15.0 and the system C compiler.
The API requires >= 3.12, but other supported-range versions have not yet been
tested. It uses the full CPython API, not the limited/stable ABI. Rebuild for the
selected interpreter and architecture.

Error buffers may truncate messages but remain ASCII; outputs change only after
successful numeric conversion. Python-level conversion may execute user code.
Tests exercise cleanup paths but do not establish absence of leaks, memory
corruption, or malicious-native-extension behavior. No proof values cross this
boundary, and no Fibril source can call it yet.

A worker protocol remains the preferred first application-facing integration;
this experiment only validates the optional direct-C route.

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
