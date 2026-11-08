# Construction reservations and committed syntax

## Use cases

Named module projects can compose separately small libraries without permanently
spending every declaration's worst-case elaboration estimate. The compiler still
requires room for each estimate before building that declaration and retains a
cumulative charge for its complete emitted signature and body. This supports
real library composition; it adds no syntax, typing rule, runtime capability or
larger numeric limit.

Use `make construction-audit` to diagnose construction refusals. It compares an
ordinary checker with a private copy that traces each declaration's reservation
and emitted-node count. Plain/traced results and CLI acceptance must agree.
The audit validates ledger continuity across modules, the reservation guard,
emitted size versus reservation, and accepted storage versus the ledger total.
For execution/allocation measurements use [composed workloads](composed-workloads.md).
Traces include observer allocation and an additional estimate traversal; they
are not CPU, heap or throughput measurements. Production code contains no tracing.

## What changed

Previously, a declaration's conservative size estimate was permanently deducted
from the project allowance. Estimates reserve space for generic 512-node inferred
types, annotations and possible cloned branch syntax. A small completed body did
not recover its unused reservation, so importing several libraries could exhaust
200000 estimated nodes despite retaining only a few thousand emitted nodes.

The unchanged preflight estimator and post-construction size guard now form a
reservation/commit protocol. Let `B = 200000`, `R` be previously committed syntax,
`E` the next estimate and `A` its emitted signature/body size:

1. Require `E <= B - R` **before** elaborating the declaration.
2. Require `A <= E` after construction; an insufficient estimate remains an error.
3. Independently check formation, typing, quantities and global references.
4. Commit `A`, release `E - A`, and carry `B - R - A` to following declarations
   and modules. Bounded mutual templates follow the same rule.

Thus committed syntax plus the active reservation must fit the same allowance.
The entry reference also needs one remaining node. Anonymous entries retain their
existing one-shot preflight/size guard. Every signature and body counts, including
erased and unused private declarations; imports/aliases do not reset the ledger.

This explicitly changes the accounting from **cumulative conservative estimates**
to **committed emitted syntax plus an active conservative reservation**. Estimates,
the 200000 ceiling, generated-IR limits, checker/reduction limits and native graph
gates are unchanged. This admits more programs and is not a proof of total
construction work, intermediate allocation, peak heap, normalization cost or time.
Existing estimator bounds remain engineering guards, not formal size proofs.

## Measured composition

Local audit at base `4cfffaf`, 2026-11-08, pinned Idris 2. Before/after checker
copies agree with their ordinary production versions.

| Entry | Previous refusal/result | Result with committed accounting |
| --- | --- | --- |
| `FullIdFour` | Accepted; 133352 estimated units, 2483 emitted nodes | Accepted; same syntax |
| `EchoThenTyped` | Accepted; 153361 estimated units, 6360 emitted nodes | Accepted; same syntax |
| `JSONThenTyped` | 163321 spent; 36679 left; next estimate 65410 | Accepted; 8308 total stored nodes; 8041 reachable graph nodes |
| `EchoJSONThenTyped` | Refused before `LSP.transition` (28855 needed, 22031 left) | Advances to an independent private-name error |

Before `JSONThenTyped.main`, only 7880 nodes were emitted, despite spending
163321 conservative units. Its main emits 428 nodes. The largest actual retained
prefix plus admitted reservation in that project is 73594, below 200000.
Its complete reachable graph passes the unchanged 8192-node binary-emission gate;
the emitted C compiles. The fixture remains an **admission probe** using fixed
`[]` plus an independent control-only typed request, not frame-body routing or
JSON-RPC decoding. It is not executed as a wire pipeline.

The original echo/JSON fixture imports `JSONThenTyped.main`, which is private.
That error was previously masked by construction rejection. It remains rejected;
no helper is silently exported. An explicitly exported temporary test copy checks
successfully, then exceeds the unchanged 8192-node native gate. Visibility and
backend admission remain separate obligations.

Local ignored reports:

- `build/benchmarks/construction-before.json`, SHA-256
  `b2748591b060d9a2a57056f51600c40ad70abc458592b8f9642b2f02ae706c29`.
- `build/benchmarks/construction-after.json`, SHA-256
  `29254ebdc384e39022f05d8c0439f9ae0635e20138f96114533626412e31061b`.

They retain source/compiler hashes and individual reservation/built events.
Historical measurement files are not rewritten.

## Validation

`tools/test_construction.py` covers ledger discontinuities and understated
reservations; composed JSON/typed checking and C compilation; visibility and native
gate rejection; many conservative declarations across modules; unused ill-typed
declarations; cumulative emitted syntax over 200000; and an oversized individual
reservation. Failed source admission produces no execution output. The separate
generated-record IR budget and other source/core/runtime regressions remain in
the ordinary suites.

The full test gate, examples and API documentation passed. The handbook was
rebuilt with local links checked and all 16 handbook tests passing; its manifest
also now includes the previously omitted native-forwarding and CommonAdmission
pages. The final 29-entry/34-execution composed matrix preserves every previously
successful entry's graph, output and native counters while recording the new
JSON/typed admission result. The new composed entry's C is compiled, not claimed
as an executed protocol pipeline.
