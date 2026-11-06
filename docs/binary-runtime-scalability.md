# Native binary continuation stack

Status: the native binary IO walker is iterative. A separately measured framing
policy now admits canonical 0..99-byte bodies; this milestone does **not** make
framing general/LSP-sized or change hosted reduction policy.

## Change and bounds

Previously, each binary bind recursively interpreted its first action and then
its continuation while retaining a C/evaluator-depth frame. A legal description
sequence could therefore exhaust the 512-depth budget even when its transport
requests and allocation were small.

The binary walker now uses an explicit continuation stack:

- Maximum **4096 pending binds**, checked before pushing another frame.
- Stack storage uses the existing 16 MiB native arena policy. Popped nodes are
  reused; storage follows peak pending depth rather than total bind count.
- Every visited description still charges the existing 100000 evaluator-step
  budget, including memoized/cyclic trusted fixtures.
- Pure expression evaluation retains its existing 512-depth bound. Transport
  request/capacity/chunk limits, EOF reservations and mandatory flush policy are
  unchanged. Legacy text/resource native runners are unchanged.

The stack contains continuation thunks, not eagerly forced action results.
Continuations are applied in the same order and pure results remain lazy. Any
transport/evaluator/stack/allocation failure stops pending work, skips the
successful-session final flush, and releases arena/session storage on represented
return. Earlier effects are not rolled back. These policies are not verified
preservation, general exception/cancellation safety or a total heap bound.

## Measurement and limitations

`examples/core/binary-many-binds.fib` is an actual checked 512-bind/flush workload.
It uses a small byte-count construction rather than an additional unary-Nat
arithmetic stressor. Compiling it against the recursive runtime at `27980d0`
returned nonzero with `native evaluation budget exhausted`; the continuation-
stack implementation completed successfully, with no byte output. Build commands
and evaluator/transport limits were otherwise unchanged. Wall-clock samples on a
loaded machine are not used as performance assertions.

The hosted default currently returns `Binary reduction budget exhausted` for
this same stress fixture. That is a separate observed limit, not a failure that
this native change fixes, and tests do not freeze that failure as required
behavior. Larger practical frames still need reduced unary-Nat/reduction work
before admitting substantially larger messages. The [framing library](binary-framing.md)
now reads each body in bulk and checks its length without a unary result, but
that does not remove the remaining numeric/reduction limits.

Separately, a temporary 99-byte framing variant succeeded on hosted execution,
the recursive native baseline and the iterative native runtime. The wire cap
was therefore extended from 32 to 99 with exhaustive length/boundary tests and
no evaluator/transport budget change. This is a measured policy extension, not
evidence that removing bind recursion alone enabled 99-byte frames.

```sh
./build/exec/fibril emit-c-binary examples/core/binary-many-binds.fib > /tmp/many.c
cc -std=c11 -I runtime/native /tmp/many.c runtime/native/fibril_binary_runtime.c -o /tmp/many
/tmp/many
make -j8 binary-scale-test
make -j8 binary-scale-test CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer'
```

## Evidence

`tools/test_binary_scalability.py` has nine tests: pending depths 0/1/511/512/
1024/4096/4097, transport failure after earlier effects, evaluator and allocation
exhaustion while pushing and after earlier effects, a 4096-action tail sequence,
lazy pure-result behavior,
and compilation/execution of the checked source fixture. Raw C fixtures inspect
private runtime internals and are **not** source-typing evidence. They verify
exact flush counts, no final flush on failure, restored evaluator depth and
exact private arena accounting showing one recycled control node for the tail
sequence.

Validation passed the unit/property phase, 163 CLI, 19 native-emitter, 7 pure-
byte/codec native, 13 binary-source, 14 raw bridge scenarios, 9 scalability, 12
framing, 9 interactive CLI, 7 editor and 16 handbook tests. Native scalability,
framing, source binary, bridge, console/resource and binary-transport sanitizer
runs passed. No timing sample or observed hosted budget failure is counted as a
successful equivalence test.

None of this adds a scheduler, concurrency or new IO permission.
