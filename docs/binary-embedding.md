# Bounded binary host embedding

Status: experimental, implemented. A trusted host can now feed bytes to a checked
Fibril binary program and receive output through explicit callbacks, without the
runtime reading stdin, writing stdout/stderr, or terminating the process.
This reuses the existing checked binary operations and transport accounting; it
is not a new unchecked source FFI or a deployed service runtime.

## Generated entry

`emit-c-binary` now supplies `fibril_program_binary_embed` in addition to its
standalone main. For example, emit the existing checked frame validator:

```sh
./build/exec/fibril emit-c-binary --source-dir examples/modules/binary-frame \
  examples/modules/binary-frame/Main.fib > frame.c
cc -std=c11 -DFIBRIL_EMBED_ONLY -I runtime/native \
  frame.c host.c runtime/native/fibril_binary_runtime.c -o worker
```

The host includes `fibril_binary_embed.h`, supplies an `FByteAdapters` table, and
calls `fibril_program_binary_embed(&host)`. Link the binary amalgamation **alone**:
do not also link `fibril_runtime.c` or `fibril_bytes.c`. One emitted program per
linked image is supported; emitted symbols are not yet application-namespaced.

The generated entry uses the compiler's existing request/capacity budgets (4096
requests, 8 MiB aggregate capacity). A lower-level trusted C host can instead use
`fibril_native_binary_embed(entry, requests, capacity, &host)` with smaller budgets.
Handwritten FEval fixtures are not proof that a program passed the Fibril checker.

## Host callback and lifetime contract

Existing `FByteAdapters` semantics apply:

- `read(context)` returns one octet in 0..255, -1 for EOF, or -2 for failure.
- `write(context, byte)` returns 0 for acceptance or -1 for failure.
- `flush(context)` returns 0 for success or -1 for failure.
- Other callback responses are contract violations, not valid data or EOF.
- Entry and all callbacks are required, even for a pure/no-IO program. A NULL
  argument returns `F_BINARY_INVALID_ARGUMENT` before evaluation or callbacks.
- The callback table is copied for the invocation. Its context is borrowed and
  must outlive the call. Callback ownership, concurrency and synchronization
  remain the host's responsibility. Do not re-enter the same transport session.
- Each run owns a separate evaluator arena and transport session. Immutable input
  chunks are retained internally until that session finishes and then freed;
  values referring to those chunks never escape to the host. Write callbacks
  receive octets, not runtime pointers.
- Callbacks must return normally. Foreign exceptions, longjmp, signals, blocking
  calls and process death are outside represented cleanup. No cancellation,
  deadlines, sandbox, stable ABI, or native memory-safety proof is supplied.

## Results and failure semantics

`FBinaryResult` distinguishes:

| Status | Meaning |
| --- | --- |
| `F_BINARY_OK` | Evaluation and required flushing succeeded. |
| `F_BINARY_INVALID_ARGUMENT` | Missing entry or host callback. No effects. |
| `F_BINARY_REJECTED` | Explicit `primRejectBytes` from the checked program. |
| `F_BINARY_PROGRAM_ERROR` | Evaluator budget, bad final result, or unsupported IO. |
| `F_BINARY_TRANSPORT_ERROR` | Admission, budget, allocation, read/write/flush failure, or invalid callback response. |

`transport_status` carries the existing `FByteStatus` **only** for transport
errors; otherwise it is `FB_OK`. In particular, evaluator failures are no longer
exposed to an embedding caller as a spurious physical adapter violation.
Messages use immutable static storage, remain valid after arena cleanup, and are
NULL on success. Branch on status values, not diagnostic wording.

On `FB_READ_FAILED`, `read_prefix` counts bytes received in the failing read.
On `FB_WRITE_FAILED`, `write_prefix` counts bytes accepted in the failing write.
These fields are zero for other statuses and are **not** cumulative totals.
Adapters must track their own total traffic if needed. An accepted output prefix
does not establish storage durability or remote acknowledgement.

Execution is incremental, unlike staged console embedding: earlier IO can remain
after a later program or transport failure. There are no implicit retries. A
physical failure poisons the session; subsequent output and mandatory final
flushing are skipped. Successful evaluation triggers a final flush; explicit
flush operations may have already flushed earlier. Failure of an explicit flush
is not retried by final cleanup. Runtime and transport allocations are released
on represented completion/failure; host-owned resources are never closed.

Existing limits remain: at most 100000 admitted requests, 8 MiB aggregate reserved
capacity, and 65536 bytes per chunk. Reads reserve their requested capacity,
including EOF/error, writes reserve their length, and explicit flush costs one
request. Final mandatory flush does not cost a request. Fixed evaluator/arena
limits and binary continuation limits still apply. Budgets do not constrain time
spent inside a host callback or guarantee that input is fully consumed.

## Checked request validation evidence

The generated integration fixture embeds `Protocol.Frame.echoFrame`, an actual
checked Fibril program, not a handwritten C parser. It accepts a canonical
Content-Length frame (including NUL and invalid UTF-8 in the body) and rejects
noncanonical lengths, truncated bodies, and a length above its 4096-byte policy.
For these parser failures it emits no response. That is behavior of **this checked
program**, not a transactional-output promise of the binary embedding API.

This is framing validation only. It does not validate JSON schemas, authenticate
requests, authorize tenants, persist messages, submit SMTP, or provide a general
HTTP/LSP server. The example consumes one frame; a host must explicitly decide
whether trailing input is legal and how requests/sessions are separated. A separate [checked enqueue worker](enqueue-worker.md) now connects a versioned
opaque-job schema to durable acceptance. It does not turn this frame echo into an
email service or add a source-level database primitive.

## Validation

```sh
# Standalone C contract tests; no Idris build required.
make binary-embedding-test
make binary-embedding-test CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer'

# Emits and embeds the checked frame program; also tests standalone execution.
make binary-embedding-generated-test
```

The public-API fixture covers 23 modes: binary/NUL echo, short input and EOF,
capacity/request/admission bounds, zero-capacity reads, partial read/write errors,
explicit/final flush behavior, invalid host responses, program rejection, late
failure after output, invalid arguments, callback-table mutation, effect gates,
and depth exhaustion. Each non-invalid mode is followed by 100 independent
successful invocations. The generated fixture covers eight framing/adapter cases,
each repeated twice, and verifies that the same generated C still runs standalone.
All embedded cases require empty process stdout/stderr. Both suites are part of
`make test` and pass with AddressSanitizer/UBSan.
