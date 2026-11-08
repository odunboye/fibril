# Native variable-argument forwarding

## Use cases

This optimization reduces lazy-call overhead when native programs pass existing
local values through helper functions, as the JSON diagnostic does while updating
parser state. Source syntax and hosted evaluation are unchanged; users do not
opt in or call a new primitive. General arguments retain ordinary lazy application.

Use [composed workloads](composed-workloads.md) for application-scale measurement.
`make json-evaluation-profile` provides exclusive evaluator-entry counters and
allocation/value counts for four existing 64-byte JSON controls. These are
diagnostics, not a JSON-RPC server or a new larger-input API.

## Profile and implementation

At base `02fa2e1`, dense 64-byte JSON used 97366 native steps. The largest
exclusive evaluator buckets were 30479 variable entries, 24037 applications
and 22274 lambda entries. Of those applications, 10763 received a syntactic
variable argument. Plain and attributed runs agreed on output and existing
metrics. Shared-global wrappers are attributed to their wrapped operation.

The emitter lowers `Apply callee (Variable index)` to `f_apply_variable`. It
evaluates the callee in the original environment, checks for a closure, and
forwards the indexed lazy cell into the usual application path. This avoids
allocating a thunk that would only evaluate `f_variable` and force that same cell
later. No argument evaluator function is emitted for this case.

The callee still runs first. Erased callees skip argument lookup. Non-erased
callees receive the original thunk without forcing it; a NULL erased slot stays
unforced until demanded. The thunk retains its memoized value, cycle state and
allocation owner. Callee-environment extension still allocates the usual binder
slot, preserving indices including erased binders. Existing force semantics
allocate in the thunk owner's region. There is no global value cache, ownership
transfer or early freeing.

Checking, quantities, whole-graph capability scans, signature/body admission and
numeric budgets remain in force. The optimization does not look through arbitrary
terms or skip checks on erased/dead syntax. Invalid raw C indices can fail at
lookup; out-of-scope arguments are outside the checked emitter contract. Trusted
C boundary probes are separate from source admission evidence.

## Measured result

Local macOS arm64/Apple clang 21 `-O2` counter comparison on 2026-11-08, with
the pinned compiler and identical workload bytes:

| Case | Steps before | Steps after | Payload before, bytes | Payload after, bytes |
| --- | ---: | ---: | ---: | ---: |
| Dense 64-byte token array | 97366 | 86811 | 3176281 | 2416105 |
| ASCII string, 64 bytes | 55258 | 50690 | 2050932 | 1721820 |
| UTF-8 string, 64 bytes | 67100 | 62532 | 2662500 | 2333388 |
| Padded scalar, 64 bytes | 42612 | 38106 | 1410393 | 1085745 |

Dense JSON spends 10.8% fewer steps and requests 23.9% less arena payload.
Thunks fall from 25011 to 14453; variable entries from 30479 to 19924.
Value and environment-cell allocations are unchanged. Peak depth falls from
81 to 74. Headroom grows from 2634 to 13189 steps under the same 100000 cap.

Outputs, consumed/accepted bytes, reads, writes, flushes, callbacks and transport
budgets match. These are work/allocation improvements, not measured wall-time
speedups. Payload excludes allocator overhead, stack and binary-session buffers;
it is not process RSS. The 64-byte parser cap, retained values, closure creation
and frontend construction blockers remain. These samples are not a soundness,
memory-safety or production throughput proof.

A later [construction-accounting change](construction-accounting.md) addresses
the reservation blocker for the fixed JSON/typed admission probe; it leaves the
parser cap and runtime measurements above unchanged.

Local raw reports (ignored artifacts):

- `build/benchmarks/json-evaluation-before.json`, SHA-256
  `a13020361e297b90d9e360da79afcc357f18718d14e98edd666e98ba5afffbbd`.
- `build/benchmarks/json-evaluation-after.json`, SHA-256
  `caecb10316a8506869ab928e58d8394893b7cabd1fcc7f070fec2dc21e89e5e5`.

Reports record source/compiler hashes, private instrumented-copy hashes,
platform/compiler metadata, input/output bytes and every bucket. Both trees were
dirty; runtime/emitter hashes distinguish baseline from prototype. Historical
expanded-tree evidence remains unchanged.

## Validation

`tools/test_native_forwarding.py` compares ordinary and forwarded calls for
memoization, unused arguments, erased calls, nested indices, preserved errors,
and a parent-owned thunk first forced inside a child region then reused after
exit. Trusted C probes and a checked hosted/native source example run under
ASan/UBSan. Audit tests cover shared-wrapper attribution and counter-only
insertions. These run in `make test` with broader hosted/native JSON, resource,
region and binary checks.

`make test`, `make examples` and `make docs` passed. The four measured JSON
cases also passed under ASan/UBSan with counters identical to the normal run.
The final composed matrix contains 29 entries and 34 execution cases. The
original entries retain their graph/check/emission admission outcomes; a
254-level reference chain now completes at depth 512, and level 255 refuses at
that same unchanged limit. The JSON-plus-typed construction refusals remain.
