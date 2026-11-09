# Portable C without heap allocation

Status: experimental output-only C11 profile with caller-owned typed pools. It
uses the existing checked native subset, including pure data/Bytes, Words and
first-order region copy-out. It provides neither a firmware image nor a specific
MCU/RTOS port, and makes no hard real-time guarantee.

```sh
make build
./build/exec/fibril emit-c-embedded examples/core/embedded.fib > program.c
cc -std=c11 -Wall -Wextra -Werror -pedantic -DFIBRIL_NO_HEAP \
  -I runtime/native program.c examples/native/no_heap.c \
  runtime/native/fibril_runtime.c -o embedded-demo
./embedded-demo
```

The [sample host](../examples/native/no_heap.c) uses static pools and a memory sink,
runs the [checked program](../examples/core/embedded.fib) three times, and verifies
`value=63` plus a newline without process IO. Replace its callbacks with an explicit
platform adapter when integrating a target.

`emit-c-embedded --source-dir ROOT ENTRY` and `--package MANIFEST` check imports
and application packages. With no arguments, the command uses `fibril.yaml`.
Emission writes C to stdout and diagnostics to stderr; it does not run the code.
It emits `fibril_program_embed_arena(host, arena)`, with no default `main` or stdio.
Both generated code and `fibril_runtime.c` require `-DFIBRIL_NO_HEAP`; the generated
header rejects a build without it. Do not use `fibril_binary_runtime.c` for this
profile. Ordinary `emit-c` and its hosted embedding API remain available.

## Storage and invocation

The [profile header](../runtime/native/fibril_embedded.h) declares:

```c
static FEmbeddedCell cells[512];
static unsigned char scratch[4096];
FEmbeddedArena arena = {
  .cells = cells, .cell_capacity = 512,
  .bytes = scratch, .byte_capacity = sizeof(scratch)
};
FNativeResult result = fibril_program_embed_arena(&host, &arena);
```

`FEmbeddedCell` is a union of the runtime's concrete storage types, so declared
arrays have the correct alignment and effective types under C's aliasing rules.
Use declared `FEmbeddedCell[]` and `unsigned char[]` arrays, not casts from an
untyped byte buffer. The cell layout is an experimental internal ABI: rebuild
host, generated code and runtime together with compatible compiler/ABI options.
Zero-initialize the descriptor as above.

The caller owns both arrays exclusively until the invocation and all callbacks
return. Capacities must describe the actual arrays. A zero-capacity pool may have
a null pointer; attempts to use it report exhaustion. The combined capacity
`cell_capacity * sizeof(FEmbeddedCell) + byte_capacity` must not exceed 16 MiB;
overflow and invalid descriptors are rejected before evaluation. Cell and byte
pools exhaust separately and are not automatically resized.

Each invocation resets allocation offsets. On return, `cells_used` and
`bytes_used` report its usage, including allocations retained on a program error.
Repeated calls reuse the same storage; the runtime does not scrub it. No value,
environment or thunk pointer escapes the generated entry. Callback bytes are
borrowed for that callback only and must be copied if the host retains output.

Reentrant calls using a different arena are supported. The same active descriptor
is refused without altering the outer invocation. Threaded callers must provide
exclusive access; the descriptor is not a lock, and aliases of active pools must
not be passed through a different descriptor. Do not change the descriptor or its
buffers during an active call. Callbacks must return normally, without `longjmp`.

Regions still check/copy first-order results. Their allocations are retained until
the whole invocation ends, including the copy-out allocation; this profile does
not reclaim subregions individually. Size pools for cumulative invocation usage.
Functions, IO and other non-first-order region results fail before callbacks.

## Checked capabilities and failure behavior

The original entry must independently check as `IO Unit`, including quantity and
termination checks. A whole reachable-syntax scan includes signatures, types,
erased arguments, dead branches and referenced global bodies. Console/file input,
file references, binary transport and binary iteration are rejected before
emission. Pure UTF-8 conversion and Bytes operations are supported. There is no
source FFI or implicit platform IO.

All output is staged and checked, including rejection of console NUL characters,
before a callback is invoked. Program/allocation failure invokes no callbacks.
The existing `FNativeHost` supplies synchronous write/flush callbacks: zero means
success, nonzero means failure. The table is copied per invocation. Writes may be
split into payload and newline calls; a successful invocation flushes once, even
with no output. Host failures may leave a visible prefix and are not rolled back.

| Result | Meaning |
| --- | --- |
| `F_NATIVE_OK` | Program and host callbacks completed |
| `F_NATIVE_INVALID_ARGUMENT` | Missing entry/callbacks, invalid capacity/pointers, or busy arena |
| `F_NATIVE_PROGRAM_ERROR` | Cell/byte exhaustion, evaluation limits or invalid runtime result |
| `F_NATIVE_WRITE_ERROR` / `F_NATIVE_FLUSH_ERROR` | Represented callback failure |

Diagnostic messages are immutable static storage, valid after return; wording is
not a machine-readable code. The runtime never calls process termination or
hosted IO in this profile.

## Portability and limits

The source uses C11 with 8-bit bytes, `uint64_t`, and a `size_t` capable of
representing 16 MiB; unsupported widths fail at compile time. The runtime and
generated objects have no `malloc`, `calloc`, `realloc`, `free` or hosted stdio
references. Ordinary memory routines such as `memcpy`, `memcmp`, `memchr` and
`memset`, plus compiler-generated support routines, may still be required from
the target toolchain. Host adapters and application/startup code must meet their
own allocation and platform constraints; arbitrary C callbacks are trusted code.

The runtime retains its fixed limits of 100000 evaluation/work entries, depth 512
and 64 output lines, plus the supplied pool capacities and 16 MiB storage ceiling.
Compiler admission retains the native subset's 8192 core-node/payload bounds.
Code, literals, the descriptor and the C stack are outside the pool counts.
Depth/step bounds are not stack-size or wall-time guarantees; measure the selected
compiler, program and hardware before making stack, latency or MCU claims.

`make embedded-test` runs strict optimized C and address/undefined-behavior sanitizer
fixtures for alignment, overflow, exhaustion, late failure, callbacks, reentrancy,
region copy-out and reuse. Checked source tests compare output with hosted C and
the reference evaluator; freestanding object audits reject allocator/stdio symbols.
The suite is included in `make test`.
