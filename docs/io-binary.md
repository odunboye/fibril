# Binary transport pilot

Status: immutable **host-side** byte values and trusted hosted/native transport
APIs with differential tests. These are not yet Fibril core constructors, source
primitives, checked C emission or an LSP implementation written in Fibril.
Existing text IO retains strict UTF-8 decoding and NUL rejection.

## Byte values

`Fibril.Data.Bytes` exports an opaque immutable value with `fromList`, `toList`,
`empty`, `byteLength`, `append`, `slice` and equality. Lists contain Bits8 octets,
not characters. Slices truncate at the end; out-of-range slices are empty. No
mutable array or pointer is exposed through these byte values. UTF-8 conversion is separate
work: this layer neither decodes nor normalizes data.

The native pilot represents read payloads as const slices in session-owned
allocations. Earlier reads survive subsequent reads. Native slices/session
pointers must not outlive the callback scope; the C API is trusted, not a checked
ownership boundary. Host byte values are ordinary immutable GC-managed data.

## Borrowed sessions

`Fibril.Runtime.Binary.withBinaryTransport requests capacity input output body`
borrows C-compatible `File` values. `withBinaryAdapters` is the trusted fault-
injection seam. The native counterparts are in `runtime/native/fibril_bytes.h`
and `.c`, separate from the existing checked-expression runtime.

- Never acquire or close a stream. The caller owns its lifetime.
- Execute sequentially; callbacks must not re-enter the session.
- Revoke host transport wrappers on every represented callback return; escaped
  wrappers reject access. Arbitrary host exceptions/abort/cancellation are not
  bracketed by this pilot. Native C callers must respect lexical scope.
- Do not execute IO during source conversion/checking. No source command or
  default output/interactive runner grants access to this pilot.

### Reads

`readBytes n transport` requires `1 <= n <= 65536`. It **fills n bytes or stops at
EOF/error**. It is not a nonblocking or POSIX read-some API: it may wait while a
short prefix is available. EOF before any data returns `Right Nothing`; otherwise
`Right (Just bytes)` returns a full chunk or a short final chunk. A following read
can observe EOF again. Empty successful positive reads are adapter violations.

A physical read failure preserves the bytes consumed before failure in
`BinaryReadFailed bytes`. NUL, invalid UTF-8, CR and LF are ordinary byte values;
none is a terminator and no replacement decoding occurs.

### Writes and flush

`writeBytes` accepts the whole declared payload or reports `BinaryWriteFailed n`,
where n is the prefix accepted by stdio, not necessarily delivered externally.
There is no appended newline or C-string conversion. Empty writes spend a request
but invoke no payload adapter. Writes can be buffered; checked flush is required.

`flushBytes` spends one request and no byte capacity. Reads do not implicitly
flush output. A caller must explicitly flush a prompt/frame before waiting for
input when the peer needs that output to proceed.

After callback success, a mandatory final flush is checked **without consuming
request fuel**, including an empty session. Callback failure does not perform
that final flush. Earlier output can remain; no rollback/durability guarantee.

### Failure and accounting

A physical read/write/flush failure, malformed adapter response or native
allocation failure poisons the session. Subsequent operations perform no IO and
report poisoned status; the first fault remains the final session outcome even
if a callback ignores it. Native buffers are freed on all represented returns,
including allocation failure after earlier successful reads.

Admission bounds are 100000 requests, 8 MiB aggregate capacity and 65536 bytes
per read/write chunk. Zero/oversize reads and capacity rejection occur before IO
and spend no request fuel. Reads reserve the requested capacity; writes reserve
their declared length. **EOF, short reads and failed operations do not refund a
reservation.** Repeated EOF therefore cannot bypass native allocation admission.
These are capacity/work policies, not equivalent heap-use, timing or total host
allocation bounds. Size/quota rejection does not itself poison a session.

Both backends use C stdio, not raw descriptor IO. This avoids losing bytes
already buffered by text reads. The default hosted adapter now uses bounded
`Data.Buffer` scratch buffers with the standard library's C `fread`/`fwrite`
support and checked `fflush`. Read counts and `ferror`/`feof` are examined
separately: a short count alone is not EOF. Error prefixes are copied before
returning. Native code and exported `stdioBinaryReference` retain the original
byte-at-a-time implementation for comparisons.

The trusted `BufferAdapters` seam can inject short progress, error/EOF flags and
invalid counts. The wrapper checks counts before copying, accumulates partial
progress within a single admitted operation, and rejects zero progress without
EOF/error. Read errors outrank simultaneous EOF. Raw callbacks must respect their
buffer bounds; this is not a safe source API. Returned `Bytes` are copied into
immutable lists, not views into mutable scratch storage. Allocation exceptions
remain outside the represented-error guarantee; this is not a packed immutable
array implementation or a general-purpose throughput claim.

POSIX/Chez is validated; Windows text-mode translation,
non-C-compatible backends, hostile concurrent stream mutation and SIGPIPE/crash
handling are not implemented or normalized here.

## Evidence

```sh
make -j8 io-binary-test IDRIS2=/path/to/idris2
make -j8 io-binary-test IDRIS2=/path/to/idris2 \
  CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer'
```

The 19-test suite builds a real hosted executable and a native C pilot. It covers
all 256 octets, NUL/invalid UTF-8 preservation, CR/LF, chunk boundaries, maximum
chunks, retained read values, quota/request policy, EOF reservations, real read
and flush failures, explicit prompt visibility and shared text/binary buffering.
It also compares both hosted adapters, runs host policy checks, fourteen block
adapter checks (progress, cumulative error prefixes, malformed counts, EOF
precedence and scratch-buffer mutation), constructor-opacity checks, and twelve native
injection scenarios including short writes, partial read failures, invalid
callbacks and allocation exhaustion with buffer cleanup. Native portions pass
AddressSanitizer/UndefinedBehaviorSanitizer; those fixtures bypass source typing.

### Block-path measurement

```sh
make -j8 io-binary-bench IDRIS2=/path/to/idris2
# Or choose 1..7 repetitions:
IDRIS2=/path/to/idris2 python3 tools/bench_binary.py --repeats 2
```

One compiled fixture transfers exactly 4 MiB in 64 KiB chunks, validates every
output byte and spends exactly 128 requests / 8 MiB admission (read plus write).
Build time is excluded; subprocess startup remains included. It reports JSON,
not flaky performance assertions. A two-sample local run measured medians:

| Adapter | Seconds | Payload MiB/s |
| --- | ---: | ---: |
| Hosted byte-wise reference | 24.960 | 0.160 |
| Hosted block path | 0.429 | 9.318 |
| Native byte-wise reference | 0.519 | 7.706 |

These are observations on a loaded development machine, not portable guarantees
or proof that the host path is faster than native generally. They support moving
the hosted default off per-byte foreign calls before exposing source operations.

### Regression/build validation

`make -j8 test editor-test` passed the unit/property phase, 161 CLI tests, 19
native-emitter tests, 9 interactive CLI tests and 7 editor tests. All focused `io-test` subtargets passed in split runs, including the new binary
suite and the existing 285 hosted checks. `make -j8 handbook` passed all 16
handbook tests.

An initial Pack test invocation resolved Fibril to a shared installed package
without the new modules. No shared installation was overwritten or cleaned.
`tools/test_units.py` now installs the already-built library under this worktree's
`build/test-prefix` and gives that private package precedence over external
curated dependencies. CLI-consuming test targets wait for this phase. The
successful regression rerun uses that isolation; the initial failure is not a
pass. The previously unindexed IO pages are registered in the handbook as well.

The block-path aggregate attempt exposed two direct-compiler environment gaps:
private installation needed `IDRIS2_DATA`, and docs needed curated package paths.
Those are now supplied explicitly, and docs wait for the installation phase.
The full CLI/editor/handbook rerun passed with an explicit compiler path. A
parallel hosted IO fixture also exceeded its 180-second compile/execute deadline;
its isolated rerun passed all 285 checks. None of these failed/timed-out attempts
is counted as a pass; all focused subtargets subsequently passed in split runs.

## Next gates toward a Fibril-written server

Block-buffer measurement and the first hosted optimization are complete; retain
the reference adapter while expanding source/runtime coverage.

1. Add checked core byte types/operations, exhaustive traversals and explicit
   binary execution admission; preserve existing runner gates.
2. Expose a small checked source API and compare actual compiled `.fib` programs.
3. Implement bounded Content-Length framing in Fibril: first one frame, then a
   bounded sequence. Test fragmentation, Unicode byte counts and truncation.
4. Add JSON/document state and a narrow compiler-service bridge.
5. Design task cancellation and ownership before concurrent source execution.

Reusable descriptions remain allowed. This is not world-token IO, a binary-file
ownership library, general exception safety or a verified runtime.
