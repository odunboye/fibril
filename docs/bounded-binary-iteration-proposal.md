# Bounded binary iteration: diagnostic milestone / proposal, not implementation

Status: **approved design; partial implementation checkpoint, NOT complete**.
The branch now has the inert core/source description and hosted/native runners;
see [implementation evidence and blocker](bounded-binary-iteration.md).
Hosted count decoding still has an allocation-before-charge gap in existing pure
Nat materialization, so full boundedness acceptance is explicitly blocked.
The measurements below remain the historical pre-implementation diagnostic.
Production `Protocol/Frame.fib` is unchanged. This is separate from pure JSON
folding/pair lowering and source state abstraction. No header parser is delivered.

## Measured cause (unchanged limits)

`tools/probe_header_loop_depth.py` checks/emits the selected source with an
explicit compiler, copies native sources to a private temporary directory, and
adds observer labels/counters only. It never modifies repository runtime files.
Each generated evaluator body and each evaluation/budget decision is unchanged.
Inputs keep stdin open. A budget rejection is an observation, not test success
for the proposed feature. Like the original probe, the tool exits nonzero on
compilation errors, wrong output or timeout, not on an observed budget rejection.

```sh
F=/Users/odunadeboye/dev/idris2/projects/fibril-byte-io/build/exec/fibril
python3 tools/probe_header_loop_depth.py --fibril "$F" --fixture nested32x32 --size 14
python3 tools/probe_header_loop_depth.py --fibril "$F" --fixture drain1024 --size 1
python3 tools/probe_header_loop_depth.py --fibril "$F" --fixture drain1024-constant --size 1
```

| Source / input bytes | Steps | Peak pure depth | Visited bind / pure / read descriptions | Outcome |
| --- | ---: | ---: | --- | --- |
| flat32 / 1 (`:`) | 2236 | 37 | 32 / 31 / 1 | success |
| nested32x32 / 1 | 63993 | 512 | 1024 / 1023 / 1 | depth rejection |
| nested32x32 / 14 | 69376 | 512 | 1024 / 1010 / 14 | depth rejection |
| nested32x32 / 32 | 76612 | 512 | 1024 / 992 / 32 | depth rejection |
| drain1024 / no reads | 58767 | 512 | 1024 / 1024 / 0 | depth rejection |
| drain1024-constant / no reads | 58261 | 25 | 1024 / 1024 / 0 | success |

Both new sources passed explicit source checking and checked native emission.
ASan/UBSan observer runs reproduced nested14 (69376steps, depth rejection) and
the constant control (58261steps, success) without sanitizer diagnostics.
`python3 tools/test_probe_header_loop_depth.py` passes three observer-seam tests;
these validate instrumentation, not the proposed iteration semantics. No broad
cold build or full framing rerun is claimed for this docs/diagnostics milestone.

The 12-line `drain1024/Main.fib` is the smaller checked/source reproducer: no
reads, ASCII table, classification or accumulator append; it just forwards empty
Bytes through 32x32 induction steps and writes them at the end. Its control
changes only `next saved` to `next primBytesEmpty`: equal empty output in this
specific experiment, **not** a valid transformation for arbitrary state.

The failing native stack after all 1024 descriptions has two write-argument
variable evaluations followed by **510 consecutive evaluations of the same
`f_variable(r,e,1)`**. In the minimized source this is the `saved` argument of
`next saved`. In the original it is the `saved` argument of `next False saved`.
For nested14 the last physical read occurs at step6395, but evaluation continues
to step69376. Thus there are two causes, not one:

1. The source explicitly invokes the remaining linear induction continuations,
   producing one pure bind per inactive transition: O(remaining allowance) work.
2. Lazy forwarding of `saved` builds unevaluated variable aliases. The final
   write forces this alias chain, causing depth rejection even though the binary
   interpreter already uses an explicit pending-bind stack. The constant control
   removes the depth failure but still performs all1024 transitions.

`runtime/native/fibril_runtime.c:evaluate_fold` already passes a **lazy**
`fold_thunk` as induction result. Eager fold evaluation is not the explanation;
an eager bottom-up fold optimization would change demand and is not proposed.
`Core/WeakHead.idr:stepHead` can instead collapse inactive pure binds during
head reduction; the hosted per-call fuel4096 then rejects the large residual
pure spine. Flat1024's hosted binary rechecking of a canonical unary Nat also
hits checkingDepth512 before effects; that is a separate gate. Existing broader
measurements remain in [header-parser-blockers.md](header-parser-blockers.md).
The historical helper-usage error is unrelated; linear continuation transport
can type-check. No alternative production source representation is attempted.

## Smallest proposed change: one inert binary-only iteration description

Proposed source interface (notation, **not available code**):

```text
LoopStep S R   = Done (1 result : R) | Continue (1 state : S)
LoopResult S R = Finished (1 result : R) | Exhausted (1 state : S)
primIterateBinary : (0 S : Type) -> (0 R : Type) ->
  (limit : Nat) -> (step : (1 state : S) -> IO (LoopStep S R)) ->
  (1 initial : S) -> IO (LoopResult S R)
```

Both types are ordinary existing finite variants/nominals, not additional core
data primitives. S/R are fixed small types, not families indexed by iteration
number; dependent counts/results and arbitrary recursion are out of scope.
The single proposed new core description has five fields: S, R, count, step,
initial. An unrestricted `step` has its ambient runtime usage scaled by
Unrestricted; `initial` is consumed once. A callback may capture reusable pure
values/descriptions, but cannot close over a linear state, resource handle or
once-effect and then execute it repeatedly. Applying the callback creates a new
action each time; memoizing the callback does not memoize/replay its first action.
No linear induction continuation is created, promoted, discarded or duplicated.

Count is a canonical finite Nat decoded by a charged, constant-C-stack traversal
at entry to this description, before its first callback/effect; malformed or
cyclic trusted counts reject within existing work limits. No new count cap is
proposed: the parser client chooses1024, while existing admission/work budgets
still bound other counts. Unary count materialization/validation can cost O(limit)
before the first effect; traversal can itself reject before any loop effects.
Even an immediate Done pays this finite decoding cost. This does **not**
construct/traverse a remaining induction spine after Done. Avoid fully normalizing/checking the
materialized count recursively at each iteration; check the original compact
count expression and perform the typed canonical traversal at execution.

Interpreter algorithm:

1. With zero count return `Exhausted initial` without invoking step or forcing
   initial. Otherwise force initial to weak-head form and pass it once to step.
2. Execute the returned IO action using the existing binary runner/session.
   Inspect its checked LoopStep outer tag, consuming its payload once.
3. Done returns `Finished result` immediately, without applying step again,
   touching unused states, or building/draining residual continuations. Its
   result retains ordinary lazy demand until a consumer asks for it.
4. Continue decrements the counter. At zero return `Exhausted state`; otherwise
   force state to weak-head form and repeat with a ready state payload, reusing
   one explicitly bounded iteration frame. Restore outer pending binds on return.

**Weak-head state demand is part of this new primitive's specified semantics**,
not a transparent optimization of natRec. It prevents the measured top-level
Bytes alias chain across iterations. It does not promise deep strictness for
arbitrary lazy fields/functions or cure source-created recursive thunks. Such
fields remain under existing fuel/depth/arena bounds; callers must demand their
own fields where necessary. No unused induction result is forced; no represented
RejectBytes or transport failure is converted to Done/Exhausted. Exhaustion
preserves the linear state for an explicit caller decision; a protocol caller
rejects rather than silently truncating. Fatal branches still must consume state
syntactically (e.g. in the continuation behind represented rejection), not gain
a generic linear discard operation.

## Boundary and accounting requirements for approval/implementation

- Binary-only capability, despite generic S/R. Other runners/emitters reject this
  description even with an apparently pure callback. Binary whole-syntax
  admission scans **all five fields**, variant payload/types, callback bodies,
  erased annotations, and dormant branches before any session effects. Hidden
  ReadLine/file scopes/references remain rejected. Returned response values have
  no executable syntax from the transport; trusted malformed native descriptions
  still receive tag/payload-shape checks and charged dispatch. Erased S/R do
  **not** permit a native runtime proof that arbitrary trusted-fixture payloads
  inhabit S/R: the general typing guarantee is source checking, not C tag checks.
- Keep request4096/capacity8388608 admission, per-request reserve-before-effect,
  poison, positive reads, final-flush-on-success-only and all existing limits.
  Iteration itself is not a transport request. Reads, writes and flushes remain
  exactly the existing operations; EOF is not an empty successful chunk, short
  reads carry their actual bytes, read-error consumed prefixes/write-error
  accepted prefixes remain errors, never Continue. A caller may consume a short
  prefix and request more, but may not retry a poisoned session.
- On failure after earlier effects, preserve already-consumed input and partial
  output: no rollback. Do not run pending callbacks or success final flush after
  rejection/evaluator/transport failure. Ordinary buffering still applies.
- Native: charge each description visit, loop transition and canonical count
  node (including memoized successors); all callback applications/forcing use
  existing enter/force accounting. Bind and iteration frames **share one**
  existing pending limit4096, not separate allowances; all use arena16MiB.
  Do not hold a pure depth entry
  across IO iterations. A cyclic ready Continue/IO fixture still spends steps
  each transition/dispatch and cannot bypass100000. Cyclic count tails spend
  traversal work; recursive forcing retains black-hole rejection. Do not charge
  skipped callback applications after Done: they are not represented work.
- Hosted: retain per-call reduction fuel4096 and checkingDepth512; charge loop
  transitions against the existing description-depth allowance4096, including
  the tail-iterated path. Count decoding requires **one explicit work ledger**
  charging BOTH successor visits (including memoized nodes) AND head-reduction
  steps; never reset weakHead4096 for each successor. Proposed count-entry ledger
  starts from the caller's fuel4096 and spends from it for either kind of work;
  this is a new bounded decoding rule, not proof of precise old-budget
  preservation. Implementation/review must document its relationship to ordinary
  per-call weakHead fuel and shared description depth, and measure the matrix.
  Avoid converting a1024 count into a term then recursively rechecking that term.
  No claim that hosted fuel and native steps are equivalent.
- Callback/state byte views stay within the current run/session arena lifetime;
  no pointer escapes or new public callback borrowing API. An iteration frame
  owns its current state/result until transferred. On failure clear pending
  references and unwind normally; session payload cleanup precedes arena cleanup
  without dereferencing borrowed views after session teardown. No per-iteration
  free of storage still reachable by a view. Arena retention remains bounded,
  not a total-heap, cancellation or quantitative-preservation claim.

Likely affected files, **only after approval**: Core/Term (and exhaustive
renaming/substitution/congruence/size/pretty/admission visitors), Core/Erased and
Runtime typing/usage, WeakHead/Reduction inert-description treatment,
elaboration primitive resolution/prelude payload/construction visitors,
Driver/Binary, Driver/Native/Emit, native runtime header/tag/construction and
binary interpreter, focused tests/docs. Full visitors make this a cross-cutting
change even though there is only one new effect description. Keep legacy
interpreters and pure JSON folding behavior unchanged. Do not implement this as
a hidden natRec optimization or move parser decisions into C/Python.

## Exact acceptance matrix for a later implementation

All applicable rows run checked source -> hosted **and** emitted native at
unchanged limits; native trusted-fixture rows also run ASan/UBSan. Record stdout,
read/write/flush/request/capacity counts, consumed prefixes, pure steps/peak depth
and arena payload. Timeouts are failures, not bounded rejection. Current source
baseline does **not** satisfy this matrix; no new primitive is implemented.

| Case | Required observation |
| --- | --- |
| early0, limit1024 | step returns Done without read; exactly1 callback,0 reads,0 Continue; initial consumed, result returned; no remaining1023 applications |
| early1/31/32/33, limit1024 | byte fixture gets `a^(n-1):`, stdin remains open; n callbacks/reads, n-1 Continue, exact `a^(n-1)` once; no later reads or residual pure binds |
| limit0 | no callback/reads; return Exhausted original linear state, no state forcing; explicit caller consumes it |
| max1024 | `a^1023:` succeeds with exactly1024 reads; compact source checks/emits under8192nodes/200000construction, hosted checkdepth512/fuel4096 and native512depth/100000steps/16MiB unchanged |
| exceed1025 | `a^1024:` exhausts after1024 reads, delimiter remains unread; caller rejects, no result output or success final flush |
| EOF/truncation | closed empty stream; prefix lacking colon; read size>1 returning short chunks then EOF: exact consumed prefix, explicit rejection, no fabricated success/extra retry |
| read/write/flush error | inject read error after prefix, short write before physical failure, final-flush failure: preserve prefixes and poison behavior, no success callback, cleanup once |
| failure after effects | step writes/flushes marker then rejects or hits pure budget; marker/prefix effects remain, later callbacks not run, no success final flush |
| demand | Done with unused divergent/over-budget dormant callback branch does not evaluate it (admission still scans it); explicit Continue state WHNF failure occurs before next step effects; lazy unused result is not forced by the loop |
| typing/capabilities | reject linear-capturing reusable callback, mismatched S/R/variant, illicit state duplication/drop; reject loop in all nonbinary runners and nonbinary capability in every erased/dormant syntax position before effects |
| trusted cycles/bounds | cyclic canonical count/ready Continue/memoized IO all spend work and reject within budgets; count may reject before loop effects; malformed outer tag/missing payload, deep callback, shared bind+iteration pending-frame and arena exhaustion fail without success flush or leaks/UAF; no arbitrary erased-S/R payload-typing guarantee |
| repeated iterations | two independent full bounds in one source session do not reset transport or native work budget; report actual work limits, not implicit per-loop allowances |
| framing regression | all existing framing cases, including two maximum4096-body frames in one session, exact opaque binary output/accounting, later-frame failure preserves earlier effects; production Frame unchanged |

A bounded byte-state fixture may meet this matrix before a full lowercase/header
parser does: the old per-octet classifier alone costs hundreds of native steps
per byte. The primitive removes residual continuation work, **not** that parser
cost or full-parser global expansion. Failure of max1024 under the same budgets
is a blocker requiring measured source simplification or a separately reviewed
change, never a blind budget increase. Pure JSON folding remains independent.
