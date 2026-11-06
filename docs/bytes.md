# Pure byte values

Status: a first checked **pure** core/source slice. This does not expose binary
transport to `.fib` programs or make an LSP server available in Fibril.
The five existing pure core constructs now have checked C lowering. See [binary transport](io-binary.md) for the trusted
host/native transport and remaining gates.

## Source primitives

| Name | Type / behavior |
| --- | --- |
| `Bytes` | Small type of immutable octet sequences, distinct from `String` |
| `primBytesEmpty` | Empty `Bytes` |
| `primBytesOctetMod256` | Linear `Nat -> Bytes`; singleton containing the low eight bits |
| `primBytesAppend` | Two linear `Bytes` arguments, immutable concatenation |
| `primBytesLength` | Linear `Bytes -> Nat`; counts octets, not characters |

The modulo operation is intentional and named explicitly: 255 gives `FF`, 256
gives `00`. It is **not** a checked-range cast. There is no implicit UTF-8
conversion, newline processing or NUL termination. `putStrLn` still requires
`String`; a byte value cannot cross that boundary by coercion.

Byte values are reusable immutable data. An explicitly linear binding must be
consumed according to the existing usage checker, but this does not imply unique
heap ownership, exactly-once effects or world-token IO.

```fibril
packet : Bytes
packet = primBytesAppend (primBytesOctetMod256 Zero)
                         (primBytesOctetMod256 (Succ Zero))

main : Nat
main = primBytesLength packet
```

The executable example is `examples/core/bytes-pure.fib`:

```sh
./build/exec/fibril check examples/core/bytes-pure.fib
./build/exec/fibril eval examples/core/bytes-pure.fib
# Normal: (Succ (Succ Zero))
```

`eval` is reference normalization, not compiled execution. No new IO command or
execution mode is added here.

## Core/checker boundary

The scoped syntax adds `BytesType`, opaque immutable `BytesValue`, `BytesAppend`,
`BytesLength` and `BytesOctet`. Erased typing distinguishes bytes, text and naturals;
usage analysis visits operands with the same linear permissions as other pure
operations. Full and head reduction agree on these contractions.

Renaming, substitution and their existing structural proofs cover all new nodes.
So do scope thinning, implicit-argument matching, abstraction, node accounting,
payload estimates and file-reference admission. This extends structural proofs;
it is not a new typed/quantitative preservation theorem.

Byte literal payload contributes its byte length to guarded candidate conversion.
A length contraction expands to unary `Nat`: candidate conversion checks that
expansion **before** allocation. Octet creation reserves its extra payload byte.
These guarded conversion policies are not general heap/time bounds for the raw
core reducer or trusted host API.

`test/src/Tests/CoreBytes.idr` checks typing/rejections, NUL/FF/invalid-UTF-8 octets,
full/head reduction, modulo wrapping, scope transport, size/payload admission,
resource scans and source linear use. CLI regressions check the actual example
and reject byte payloads through every existing text execution/emission command.

## Native pure byte values

`runtime/native/fibril_runtime.c` now gives byte values a separate `V_BYTES` tag,
not a string alias. Payloads are explicit pointer/length pairs with no terminator
or decoding. Generated literal arrays are static immutable decimal octets;
append and singleton payloads live in the existing run-owned allocation arena.
Raw C literal callers must keep storage immutable/alive through the run. Empty
literal storage may be null, but nonempty null literals are rejected.

Append checks operand tags, addition overflow and the existing allocation budget.
Length constructs the existing unary native Nat representation. Length expansion
and modulo traversal charge native evaluation steps even for memoized nodes;
malformed cyclic trusted naturals cannot bypass that bound. Native depth,
allocation and step limits remain distinct from hosted reduction budgets, so
large inputs can exhaust one backend earlier. No preservation or heap-bound
proof is claimed.

`examples/core/bytes-native.fib` computes a byte length and renders it as text:

```sh
./build/exec/fibril run examples/core/bytes-native.fib
./build/exec/fibril emit-c-interactive examples/core/bytes-native.fib > /tmp/bytes.c
cc -std=c11 -I runtime/native /tmp/bytes.c runtime/native/fibril_runtime.c -o /tmp/bytes
/tmp/bytes
# xx
```

This is real checked source emission/execution, but the output remains text. It
neither reads nor writes binary streams. The existing output-only, interactive
and resource entry points gain no new IO permission.

```sh
make -j8 bytes-native-test
make -j8 bytes-native-test CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer'
```

The suite compares hosted execution and compiled checked source in both emission
modes, checks that generated C retains byte operations (not just a precomputed
result), and exercises thirteen raw ABI cases: all octets, null empty storage,
modulo values 0..513, type errors, overflow, missing callbacks, cyclic naturals
and evaluation/allocation exhaustion. A separate raw case rejects Bytes as text
output. These raw cases intentionally inspect runtime internals, not source
checking. Two checked-core fixtures verify literal NUL/FF/invalid-UTF-8 decimal
emission without character conversion.

## Validation

The unit/property phase (including 28 deterministic core-byte checks), 163 CLI,
19 native-emitter, 9 interactive CLI, 7 editor and 16 handbook tests passed.
Focused IO subtargets passed in split runs: 290 hosted checks, 29 checked
resource differentials, console/interactive emission comparisons, and 19 binary
transport tests. Native console/resource/binary suites passed ASan/UBSan.

On this loaded machine the fresh hosted fixture exceeded its default 180-second
compiler/execute deadline. Its successful rerun used:

```sh
FIBRIL_IO_TIMEOUT=450 make -j8 io-hosted-test IDRIS2=/path/to/idris2
```

The override is bounded to 1..900 seconds; default remains 180. The hosted harness
now terminates its own compiler-wrapper process group on timeout/interruption.
A shell/child timeout smoke check passed. Parallel console/interactive fixture
builds also timed out; their isolated reruns passed at the existing deadlines.
No timed-out invocation is counted as a successful test.

## Remaining work

- Bounded indexing/slicing and explicit fallible UTF-8 conversions.
- Checked binary descriptions, explicit hosted/native runners and source
  admission. The [transport pilot](io-binary.md) remains internal.
- A real Fibril-written bounded Content-Length parser and echo program.
