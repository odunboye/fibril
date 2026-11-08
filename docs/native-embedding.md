# Native embedding: first production-runtime slice

Status: experimental, implemented for the existing staged console subset.
This is a host integration boundary, **not** a general source-language FFI,
network/database adapter, daemon runtime, or production-readiness claim.

## Using checked generated code

Normal `fibril emit-c` now supplies `fibril_program_embed` as well as its existing
standalone `main`. Build with `FIBRIL_EMBED_ONLY` to omit that main and link your
own trusted host:

```sh
./build/exec/fibril emit-c examples/core/hello-world.fib > program.c
cc -std=c11 -DFIBRIL_EMBED_ONLY -I runtime/native \
  program.c host.c runtime/native/fibril_runtime.c -o worker
```

An illustrative `host.c` (the callbacks could instead use a bounded application
buffer or an explicitly owned stream):

```c
#include "fibril_runtime.h"
#include <stdio.h>

static int write_bytes(void *context, const unsigned char *bytes, size_t length) {
  return fwrite(bytes, 1, length, (FILE *)context) == length ? 0 : 1;
}
static int flush(void *context) {
  return fflush((FILE *)context) == 0 ? 0 : 1;
}
int main(void) {
  FNativeHost host = { stdout, write_bytes, flush };
  FNativeResult result = fibril_program_embed(&host);
  if (result.message) fprintf(stderr, "worker: %s\n", result.message);
  return result.status == F_NATIVE_OK ? 0 : 1;
}
```

This example intentionally chooses stdout; the embedding runtime itself does
not access process stdio. Only ordinary `emit-c` supplies this generated entry.
Interactive, resource and binary runners keep their existing APIs and gates.
Link one generated program per image: emitted global/entry names are not yet
namespaced for linking independently generated applications together.

## Contract

- The program is checked before emission under the existing backend capability
  gates. Calling raw `fibril_native_embed(FEval, host)` from handwritten C does
  not provide typing or linearity evidence.
- Entry, host, write and flush callbacks are required. Invalid arguments return
  `F_NATIVE_INVALID_ARGUMENT` without evaluating the program or invoking a callback.
- Evaluation, complete action planning, final Unit validation and **all** staged
  output NUL checks finish before the first callback. Program failures return
  `F_NATIVE_PROGRAM_ERROR` without host output or flushing.
- Output is length-delimited UTF-8 bytes under the existing text rules. Each
  console action ends with a newline; callbacks can receive text and newline as
  separate writes. Empty text still produces its newline.
- Callbacks return zero for success and nonzero for failure. The first write
  failure stops subsequent writes and skips flushing (`F_NATIVE_WRITE_ERROR`).
  Successful output is flushed once, including a pure/no-output program; a flush
  failure returns `F_NATIVE_FLUSH_ERROR`. There is no automatic retry.
- A callback may already have caused partial effects before returning failure.
  These effects cannot be rolled back. A successful write does not mean durable
  storage or remote acknowledgement; the adapter must define its own guarantees.
- The byte pointer is borrowed **only for the duration of that callback**. Copy
  it if retaining output. The host owns its context, which must remain valid
  throughout the call; the runtime neither frees nor retains it after returning.
- Each synchronous invocation owns and frees its runtime arena on represented
  success/failure. No `FRuntime`, `FEnv` or `FValue` is returned to the host.
  Result messages have immutable static lifetime, with NULL on success. Branch
  on the status enum, not diagnostic wording.
- The callback table is copied at entry. Mutating the caller's table from a
  callback cannot redirect the active run. Nested invocations have independent
  arenas; the host is responsible for synchronization of shared callback state.
- Callbacks must return normally. Signals, process termination, arbitrary memory
  faults, cancellation, longjmp and foreign exceptions are not caught. Do not
  unwind across C runtime frames. Callbacks are trusted native code and may
  themselves allocate, block or access stdio.
- Existing fixed limits remain: 100000 evaluation/planning entries, depth 512,
  64 console actions and 16 MiB requested arena payload. Callback time/memory,
  allocation bookkeeping and C stack are not covered. This is not a sandbox,
  hard-real-time guarantee, or stable/versioned binary ABI.

The legacy `fibril_native_run` retains its process-console behavior. The new
embedding path deliberately prevalidates all staged text before host effects;
this does not silently broaden the capabilities of any legacy runner.

## Validation

```sh
# No Idris build needed: 17 trusted-C adversarial scenarios.
make native-embedding-test
make native-embedding-test CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer'

# Builds the compiler, emits real checked source, tests embedding and standalone.
make native-embedding-generated-test
```

Fixtures cover invalid arguments, pure results, UTF-8/empty/multiple lines,
write/newline/flush failures, late NUL, late non-Unit result, missing evaluation
result, depth exhaustion, rejected resource/input effects, nested calls, callback
table mutation, and 1000 sequential invocations. Host failures and program
failures are followed by a successful independent run. Every embedded fixture
must leave process stdout/stderr untouched. Generated integration also checks
three invocations of a real Fibril program and its legacy standalone execution.
Both new suites are included in `make test`.

## Next gates toward a native worker

1. Define validated foreign request/response data and ownership; no arbitrary C
   pointers or unchecked values should become Fibril terms.
2. Add one explicit capability (for example durable queue operations), with
   represented errors, adapter-owned resources and deterministic fault injection.
3. Decide per-request lifetime, cancellation, timeouts and shutdown cleanup;
   synchronous console callbacks alone do not constitute a service runtime.
4. Integrate maintained SQLite/network/TLS libraries through that boundary,
   test crash recovery and uncertain submission, then deploy a bounded worker.

Do not expose source primitives until admission, hosted behavior, native behavior
and failure/resource semantics have agreement tests. The existing email model
remains a pure model, not a networked or durable service.
