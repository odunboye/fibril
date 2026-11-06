# Checked binary IO

Status: working standalone `.fib` execution via explicit hosted
`fibril run-binary PATH` and checked native `fibril emit-c-binary PATH`.
The [trusted transport](io-binary.md) and [pure bytes](bytes.md) are separate
layers. A [bounded canonical framing library](binary-framing.md) now exists;
there is no LSP implementation yet.

## Source descriptions

| Primitive | Contract |
| --- | --- |
| `ByteReadResult` | Structural EOF/chunk result; reads produce linear nonempty chunks |
| `primReadBytes` | Linear `Nat -> IO ByteReadResult`; positive capacity <=65536 |
| `primByteReadCase` | Erased result type, linear result, unrestricted EOF/chunk branches; chunk consumes one linear `Bytes` |
| `primWriteBytes` | Linear `Bytes -> IO Unit`; no newline, decoding or C string |
| `primFlushBytes` | `IO Unit`; checked explicit stdout flush |
| `primRejectBytes` | `IO Unit`; represented binary-only program rejection, no transport request |

The result is a structural variant alias, not a refined/nominal provenance type;
nonempty chunks are a read-operation output contract, not a proof about every
raw inhabitant of that type.

These construct inert descriptions. Checking, normalization and C emission do
not execute them. Descriptions remain reusable unless explicitly bound linearly;
this is not world-token IO or an exactly-once effect/ownership theorem.

A read **fills capacity or stops at EOF/error**, not POSIX read-some. A short
nonempty final chunk is followed by EOF on another read; EOF before any bytes is
the EOF alternative. There is no implicit newline handling, NUL filtering or
replacement decoding. `primByteReadCase A result eof chunk` branches cannot
capture linear ambient resources through unrestricted application.

Unlike text `ReadResult`, physical binary read errors are **fatal runner errors**,
not a third result alternative. The public hosted `BinaryTransportFailure
(BinaryReadFailed bytes)` retains the consumed prefix; CLI diagnostics report its
length without writing raw bytes. Write failures retain the accepted prefix
count, not a delivery/durability guarantee. Malformed responses poison transport
state, and the first physical fault remains the session outcome.

## Executable examples

`examples/core/binary-echo.fib` echoes one chunk of at most two bytes:

```fibril
main : IO Unit
main = bind ByteReadResult Unit (primReadBytes (Succ (Succ Zero))) (\(1 result : ByteReadResult) => primByteReadCase (IO Unit) result (pure Unit ()) (\(1 bytes : Bytes) => primWriteBytes bytes))
```

```sh
printf '\000\377' | ./build/exec/fibril run-binary examples/core/binary-echo.fib | od -An -tx1
# 00 ff
```

`examples/core/binary-echo-loop.fib` uses ordinary Nat recursion and reusable IO
descriptions to process at most sixteen two-byte chunks. EOF iterations still
spend capacity. These are bounded transport demonstrations, not the framing parser or a server;
see the separate [Fibril framing library](binary-framing.md). The one-chunk example deliberately leaves any input
beyond its capacity unread.

## Execution/admission

The hosted binary entry borrows stdin/stdout C-compatible FILE streams, never
opens/closes them, and uses the same stdio buffering family as text IO. Explicit
flush is required before waiting for a peer that needs pending output. Successful
main completion checks a mandatory final flush without spending request fuel.
Callback/description failure skips that flush; buffered earlier output may still
exist or be flushed by the process/caller. There is no rollback guarantee.

CLI defaults: description depth 4096, per-normalization fuel 4096, 4096 transport
requests and 8 MiB aggregate capacity. The transport admits at most 100000
requests / 8 MiB / 65536-byte chunks. Reads reserve declared capacity, writes
reserve length, and EOF/short/errors receive **no refunds**. Empty writes spend a
request without a payload callback. Explicit flush spends a request, no capacity.
Invalid size/quota rejection spends no request. These are distinct policies, not
global time or heap bounds.

Initial syntax is capped at 8192 nodes and 8192 literal payload units; the public
hosted driver caps description depth at 8192 and normalization fuel at 100000.
Each head/response/continuation is checked incrementally. Later computation can
fail after earlier effects; represented transport errors remain distinct from
kernel/reduction/description failures. An internal driver-error channel prevents
non-transport failure from being reported as callback success/final-flush success.

A new exhaustive whole-syntax visitor scans branches, annotations, motives,
recursive constructors and nominal inventories **before execution**:

- Output planning, interactive preparation, resource execution and all existing
  C emission modes reject binary requests, even in dormant/erased fields.
- Binary execution rejects text IO, file operations/types and runtime references,
  even when hidden in dormant fields. It does not acquire a file capability.

Only `emit-c-binary` grants native binary execution. Existing C modes reject
these descriptions rather than silently repurposing text IO.

Hosted wrappers are revoked on represented return; streams remain caller-owned.
Arbitrary host exceptions, signals/SIGPIPE, crashes, task cancellation and
concurrent mutation are not normalized or bracketed by this milestone. No
scheduler, public source scoped-file API or compiler-service bridge is added.

## Native binary execution

```sh
./build/exec/fibril emit-c-binary examples/core/binary-echo-loop.fib > /tmp/binary.c
cc -std=c11 -I runtime/native /tmp/binary.c runtime/native/fibril_binary_runtime.c -o /tmp/binary
printf '\\000\\377' | /tmp/binary | od -An -tx1
# 00 ff
```

Compile `fibril_binary_runtime.c` **instead of** `fibril_runtime.c`. It is an
explicit amalgamation of the pure runtime and binary transport, reusing their
private evaluator/session implementation. Do not additionally link either
`fibril_runtime.c` or `fibril_bytes.c`; that would duplicate symbols. Legacy native
build commands still compile only the original runtime and gain no binary entry.

`Binary` lowering checks the complete original term and rejects text/resource IO
before generating code. The separate C interpreter accepts only pure, bind,
read-bytes, write-bytes, flush and represented rejection descriptions. It uses the established byte
session for reservations, prefix failures, poisoning and final flush. Read
buffers and all derived byte/String views remain live through the callback;
final Unit is forced before session storage is freed. Pure arena teardown then
walks allocation metadata without inspecting freed byte views.

The runner keeps evaluator errors distinct from physical transport failures.
Read/write diagnostics retain the current operation's consumed/accepted count;
source physical errors remain fatal. The typed hosted API retains the full read
prefix; the native process interface returns status/diagnostics, not that payload.
Callback failure skips final flush, successful Unit completion checks it without
request fuel. Native evaluator depth/steps/arena bounds differ from hosted
reduction policy. Binary bind traversal now uses a [bounded continuation
stack](binary-runtime-scalability.md) (4096 pending binds, recycled arena nodes)
rather than retaining C/evaluator depth. Pure evaluation still has the existing
512-depth limit. Either backend can reject larger computations earlier. No verified
preservation, general exception/signal/cancellation safety or total heap bound
is claimed.

## Evidence

```sh
make -j8 binary-source-test
make -j8 binary-source-test CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer'
make -j8 binary-runtime-test
```

`Tests.BinaryDescriptions` checks typing, inert reduction, conservative admission,
all legacy runner gates, all-octet hosted execution, full reservation on short
reads, EOF, typed partial-read/write failures, request/flush accounting and no
mandatory flush on driver failure. `tools/test_binary_source.py` runs actual
`.fib` chunks/sequences over all octets, empty/short input, explicit flush-before-
input, real stdout failure, zero reads and dormant cross-mode requests. It cleans
up only its own child process groups. Native source tests compile the actual
examples and compare all-octet/EOF/short/prompt/error behavior to hosted execution.
`tools/test_binary_native.py` adds fourteen raw bridge scenarios for capacity,
prefixes, request/flush policy, allocation/admission failures and arena/session
cleanup. The source integration suite also carries read-backed byte views
through slice/UTF-8 conversion and back to binary output. These trusted C
fixtures are not source-typing evidence.

Validation passed the unit/property phase (33 binary description/interpreter
checks), 163 CLI, 19 native-emitter, 7 pure-byte/codec native, 13 binary-source,
9 interactive CLI, 7 editor and 16 handbook tests. Focused IO subtargets passed
in split runs, including 306 hosted checks and 29 resource differentials. Native
console/resource/byte/codec/binary suites passed ASan/UBSan; the hosted compiler
and its foreign library are not thereby sanitizer-verified. The hosted fixture
used the existing explicit 450-second test deadline; no old runner budget was
increased.
