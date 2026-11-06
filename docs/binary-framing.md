# One bounded frame, written in Fibril

Status: a working **Fibril-written** canonical Content-Length parser/echo library,
checked and executed through hosted and native binary IO. This is not a general
LSP header parser, unbounded server, JSON implementation or self-hosted LSP.
A second client demonstrates an explicitly bounded two-frame sequence.

## Contract

The accepted wire format is exactly:

```text
Content-Length: N\r\n\r\n<body of N bytes>
```

- `N` is canonical decimal **0..4096**, one to four digits, no leading zeros except
  the single digit `0`. A fifth digit or a value above 4096 is rejected before body
  consumption. Arithmetic is bounded; there is no unbounded decimal accumulator.
- Header spelling/case, one space and CRLF terminators are exact. No additional,
  duplicate or optional headers, LF-only lines, whitespace variants, signs or
  content types are accepted by this first pilot.
- Body length counts bytes, not Unicode characters. Arbitrary octets, NUL,
  malformed UTF-8 and newlines are opaque body data.
- One frame is expected. EOF before/within it is rejection, not a normal empty
  stream. Input beyond the first frame is left uninterpreted, not echoed. C stdio
  may already have buffered more bytes; no raw descriptor handoff is promised.
- Header and complete body are validated/buffered before echoing. Malformed or
  truncated input produces nonzero status and no frame output. A complete frame
  is echoed/flushed without waiting for stdin EOF.

These strict limits are deliberate admission for an initial executable parser,
not claims of full LSP/RFC header acceptance. Broader header/size policy and
server lifecycle remain future work.

## Code and execution

The protocol logic is in
`examples/modules/binary-frame/Protocol/Frame.fib`; `Main.fib` is only a client
importing its exported `echoFrame : IO Unit`. Decimal classification, length
bounds, header/terminator checks, body assembly and echo decisions are Fibril
code. There is no C or Python framing parser used by execution.

```sh
ROOT=examples/modules/binary-frame
ENTRY=$ROOT/Main.fib
./build/exec/fibril check --source-dir "$ROOT" "$ENTRY"
printf 'Content-Length: 4\r\n\r\nping' | ./build/exec/fibril run-binary --source-dir "$ROOT" "$ENTRY"
./build/exec/fibril emit-c-binary --source-dir "$ROOT" "$ENTRY" > /tmp/frame.c
cc -std=c11 -I runtime/native /tmp/frame.c runtime/native/fibril_binary_runtime.c -o /tmp/frame
printf 'Content-Length: 4\r\n\r\nping' | /tmp/frame
```

Binary `--source-dir ROOT ENTRY` checks the complete module graph before any
execution/emission. It is an explicit root and entry path, not package discovery.
Legacy output/interactive/resource/native modes still reject binary requests.

`Two.fib` uses a local reusable IO description to process exactly two frames.
Use the same commands with `ENTRY=$ROOT/Two.fib`. Each validated frame is flushed
before the next is read, so peers may wait for each echo before sending another.
A failure in frame two leaves frame one's already-flushed output intact. EOF
before the second frame is a rejection. This is a bounded sequence, not a
cancellation-safe or concurrently scheduled server.

## Bulk body reads

After validating the header, a positive body length causes exactly one
`primReadBytes count` request. The transport fills that capacity or stops at
EOF/error; fragmented writes do not require a source-level per-byte loop.
`primBytesLengthIs count body` verifies the returned length before assembling
and echoing the frame. EOF or a short body rejects without output. Zero-length
bodies skip the read entirely, preserving the prohibition on zero-capacity reads.

This removes the per-byte append loop: the complete body is appended to the
header once. A 99-byte frame uses **8 requests instead of 106**, with the same
**242 bytes of reserved capacity** (121 read, 121 written). A zero-byte frame
uses 6 requests/42 capacity; a short 99-byte body still reserves its full read
capacity. The successful-session final flush does not spend a request.
The per-byte baseline at `91a1899` was independently compiled and instrumented
to confirm 106/242, rather than inferring the count from elapsed time.
An instrumented native runner checks these counts around the actual generated
Fibril program; it does not implement the parser.

`primBytesLengthIs : (1 count : Nat) -> (1 bytes : Bytes) -> Bool` compares byte
lengths without building a unary `Nat` result. It is a pure data operation, not
an exact-read effect or a refinement type. Native input-Nat traversal still
charges evaluator work and lazy operands can still allocate; there is no
constant-time or total-allocation claim. Protocol limits are 0..4096 bytes.

Decimal accumulation now uses bounded force-shared byte buffers, avoiding the
Nat-fold work that exhausted both backends at 4096. The source checks the four-
digit boundary before constructing the final accumulator. No runtime budgets
were increased. See [numeric probes and 4 KiB framing](binary-numbers.md).

## Supporting operations

`primRejectBytes : IO Unit` is an inert **binary-only** represented rejection.
The selected runner reports `Binary program rejected input`, spends no transport
request, and performs no mandatory successful-session flush. It is not a generic
exception, cancellation or rollback facility. Already-performed effects from an
arbitrary program may remain; this library deliberately writes only after frame
validation.

`primBytesShare` has core type linear `Bytes -> Box unrestricted Bytes`; it consumes a byte
value into a reusable immutable byte box. A source record supplies its public
view:

```fibril
record SharedBytes : Type where
  constructor Shared
  bytes : Bytes
```

`case primBytesShare input of Shared bytes => ...` may reuse `bytes`. This is a
**Bytes-specific** copyability operation: it cannot share IO descriptions,
Strings, resource handles or arbitrary types. It does not confer permission to
repeat effects. Host byte values are immutable; native values share immutable
arena/static/session storage, not mutable pointers. Native box elimination uses
the existing unary runtime representation. Structural proofs and usage analysis
cover the new operations; no new quantitative preservation theorem is claimed.

The first nominal-state parser prototype exceeded the existing 200000-unit
expanded-core construction policy. No budget was raised. The working library
uses lexical helper sharing and continuation-style state to fit current source/
core limits; immutable byte sharing avoids expensive linear-data reconstruction.
This is an implementation constraint, not a claim that unrestricted application
or compiler scalability is generally solved.

## Evidence

```sh
make -j8 framing-test
make -j8 framing-test CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer'
```

`tools/test_framing.py` is only a process client. It compiles the actual module
entry, then compares hosted/native behavior for all lengths 0..99, larger boundaries and 4000..4096, all 256
body octets, Unicode byte counts, every truncation offset of a sample and every short-body length below 99, malformed/
over-limit lengths, strict header syntax, trailing data and fragmented writes.
Its open-input test keeps stdin open after sending a complete frame and requires
the echoed frame and successful exit, proving the program does not wait for EOF.
Two-frame tests compare different bodies, check non-rollback on later rejection,
and wait for each echo before sending the next frame. The suite has fourteen test
methods over these hosted/native matrices.
Native tests run under ASan/UBSan; this does not verify the hosted compiler/FFI,
source preservation, arbitrary exceptions, signals or concurrent mutation.

Validation passed the unit/property phase, 163 CLI, 19 native-emitter, 7 pure-
byte/codec native, 13 binary-source, 14 raw bridge scenarios, 14 framing, 6 numeric-probe tests, 9 binary-scalability, 9
interactive CLI, 7 editor and 16 handbook tests. All focused IO subtargets passed
in split runs, including 306 hosted checks and 29 resource differentials. Native
framing/byte/codec/console/resource/binary suites passed ASan/UBSan. The hosted
fixture used the existing explicit 450-second test deadline, not a runner-budget
increase.

The body cap was extended from 32 to 99 only after testing both backends and
the recursive native baseline at 99. The separate [binary continuation stack](binary-runtime-scalability.md)
improves deeper IO workloads; it is not credited with making 99-byte frames
possible. The subsequent 4 KiB extension uses measured source-level numeric
handling, not larger evaluator budgets. Tests include two maximum-sized frames,
large fragmented input and oversize rejection without waiting for body/EOF.

The existing evaluator, allocation and transport limits still apply. This is a
single-frame building block toward an LSP application, not that application.
