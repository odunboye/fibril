# Bounded binary iteration — implementation checkpoint, NOT complete

**Blocking limitation:** hosted count decoding charges head contractions and
successor visits from one ledger, but the existing pure reducer can allocate a
unary natural **before** that ledger charges its successor visits. In particular,
`stepHead (BytesLength (BytesValue bytes))` calls `naturalTerm` inside one step.
A derived large byte value can therefore allocate an oversized count before
rejection. Nested NatRec/byte-primitive full-step paths have the same issue.
The checked API below exists on this branch, but is **not delivered as satisfying
all bounded-iteration safety requirements**. Passing tests below do not close
this allocation-before-charge gap.

The approved follow-up is a count-only bounded reduction path that checks and
charges unary materialization **before allocating**, from the same ledger, at
all demanded nested operands and full-step fallbacks. It must also charge
canonical-natural/low-octet traversals used by byte operations. A top-level
BytesLength special case or a preguard followed by unchecked recursive
`stepHead`/`step` is insufficient. Do not change generic weakHead/natRec demand,
raise budgets, or add a separate count cap. This checkpoint deliberately does
not attempt a rushed copy/refactor of the exhaustive pure reducer.

## Implemented interface and behavior

```text
LoopStep S R   = structural variant [linear R, linear S]
LoopResult S R = structural variant [linear R, linear S]
primIterateBinary : (0 S : Type 0) -> (0 R : Type 0) ->
  (limit : Nat) -> (step : (1 state : S) -> IO (LoopStep S R)) ->
  (1 initial : S) -> IO (LoopResult S R)
```

Tags are positional: **0** means Done/Finished and carries one R payload;
**1** means Continue/Exhausted and carries one S payload. Constructors are
`primLoopDone`, `primLoopContinue`, `primLoopFinished`, `primLoopExhausted`,
with explicit erased S/R arguments. Eliminators `primLoopStepCase` and
`primLoopResultCase` take S, R, an erased result type, a linear scrutinee, and
unrestricted R/S consuming branches. These are forgeable ordinary structural
aliases, not source provenance/refinement guarantees.

S/R must inhabit Type0; step must have exactly the linear argument and variant
result above. Ambient step usage scales Unrestricted, preventing reusable
callbacks from capturing linear external state/handles/once-effects. Initial
usage is once. No linear induction continuation or generic linear discard is
introduced. The source count parameter is Unrestricted as specified by its
unannotated binder. Direct core count usage is once: the interpreter decodes it
once. An unrestricted wrapper binder may be used once; source application still
scales its argument conservatively. Tests distinguish the raw linear-count case,
source rejection of a linear count argument, and forbidden count/initial aliasing.

Count decoding precedes any callback, including early Done. Zero returns the
original initial state without forcing it or step. Before every actual callback,
state is forced to WHNF. This is **new primitive semantics**, not a natRec/fold
optimization. Every application creates a fresh action, even when the callback
closure or a reusable inert read description is memoized. Done stops immediately
without remaining callbacks/spines; R remains ordinarily lazy. A final Continue
returns Exhausted without forcing its state. Deeper lazy state fields can still
fail existing pure budgets; there is no deep-strictness promise.

Whole-syntax binary admission scans all five fields, including erased type
annotations, variant payloads and dormant branches, before effects. All old
hosted/output/interactive/resource/C modes reject the loop even at zero count.
Binary rejects hidden text/read-line/file/reference capabilities. Native erases
S/R and checks only the outer variant tag/payload shape; it cannot establish
arbitrary runtime payload types in malicious trusted FEval fixtures.

## Accounting and lifetimes

No existing constants/defaults were raised: hosted description depth4096,
per-call reduction fuel4096, checking depth512/type-reduction fuel128,
requests4096/capacity8388608; source initial/node8192 and construction200000;
native steps100000, pure depth512, arena payload16MiB, pending4096.

Current hosted `decodeCount` has one ledger initialized from caller fuel4096.
Every recursive successor visit or head contraction consumes one unit; terminal
inspection requires positive remaining work. It does not refresh weakHead4096
per successor, and it does not infer/check the materialized unary count again.
Original compact source is checked first. Ordinary state/action/result weakHead
calls still receive the existing per-call fuel independently of this entry
ledger. The pre-materialization hole described above remains a blocker.

Within a hosted loop, each callback transition monotonically decreases the
existing description-depth allowance; callbacks execute with the remaining
allowance under existing recursive-description rules. This is not a global
counter of every sibling description: independent loops retain ordinary
per-call depth behavior. Transport quotas remain shared for the entire session.

Native count successor visits, description dispatches and loop transitions are
charged even for ready/memoized/cyclic fixtures. Native count construction via
`byte_natural` is already charged. Bind and loop frames share **one** pending4096
stack and one arena. Iterations retain no pure/C depth entry across IO. Native
work/arena/transport budgets do not reset between independent loops. Hosted and
native work budgets are intentionally **not equivalent**.

Loop dispatch is not a transport request. Existing read/write/flush reservations,
positive reads, poison, prefixes, EOF/short/error distinctions, borrowed streams,
final-flush-on-success-only, and no-rollback behavior remain unchanged. On failure
there are no later callbacks or success flush. Session payload teardown precedes
arena cleanup; pending references are not dereferenced afterward. Immutable arena
and session views remain run-local; there is no new public borrowing API or
per-iteration free of reachable storage. Arena payload is not total heap usage.

## Field/visitor coverage

All five fields are included by:

- Term rename, substitution, syntax equality; renaming and substitution
  congruence/identity/composition proofs (including mixed compositions).
- Erased inference and runtime usage analysis (S/R erased in usage, still typed
  and scanned); full pure reduction traversals; head reduction remains inert.
- Effect admission, resource-reference admission, core size/nominal occurrence,
  pretty printing.
- Elaboration abstraction, thinning, substitution-node estimation, payload weight,
  conversion admission/safe-redex scanning, parameter matching and implicit type
  inference.
- Native emission (three computational fields after full five-field admission).

Legacy interpreters are unchanged; the shared capability scan rejects loops.
`Protocol/Frame.fib`, header parsing, pure JSON, byte-io sibling worktree, LSP,
shared installations and shared caches were not modified.

## Reproducible checkpoint validation

Use the pinned Idris2 through explicit IDRIS2; all package installation is confined
to `build/test-prefix`. `tools/test_binary_iteration.py` creates a private .ipkg
with `depends = fibril, yaml`, so the builder resolves transitive dependencies.
It filters cached Fibril and Pack warning text from curated paths, never runs gc,
and never installs external packages. No polling/background loops are used.

```sh
make -j8 binary-iteration-test IDRIS2=/path/to/pinned/idris2
```

The bounded foreground run passes **11 test groups**, including checked source
hosted/emitted native and separately labelled trusted raw C tests. Source/native
observer copies insert counters only, never alter budget decisions. Raw fixtures
run normally and with `-fsanitize=address,undefined -fno-omit-frame-pointer`.
Timeouts fail, never count as bounded rejection. Counts/work observations are
printed as `ITERATION_ROW` records. `METRICS` means reads, writes, flushes,
unconsumed input bytes, output bytes; hosted writes count payload adapter calls
(empty writes skip that adapter), while native writes count descriptions.
`BUDGET` is native requests/capacity reserved; `NATIVE` is steps, peak pure depth,
arena payload, callback applications. Hosted reservation counts for these fixed
fixtures follow from checked request sizes, not an exported session-statistics API.

| Case, allowance1024 | Callbacks/reads | Output | Native steps / peak / arena payload | Request/capacity reservations |
| --- | ---: | ---: | --- | --- |
| early0, Done without reading | 1 / 0 | original 1-byte state | 3214 / 12 / 103793 | 1 / 1 |
| early1 (`:`) | 1 / 1 | 0 | 3354 / 20 / 109120 | 2 / 1 |
| early31 | 31 / 31 | 30 | 5882 / 20 / 200065 | 32 / 61 |
| early32 | 32 / 32 | 31 | 5966 / 20 / 203104 | 33 / 63 |
| early33 | 33 / 33 | 32 | 6050 / 20 / 206144 | 34 / 65 |
| max1024 | 1024 / 1024 | 1023 | 89294 / 20 / 3710320 | 1025 / 2047 |
| exceed1025 | 1024 / 1024 | 0; delimiter unread | 89305 / 20 / 3710832 | 1024 / 1024 |

The delimiter fixture is a byte-state diagnostic, not a header/JSON parser. Naive
wrapper-heavy source first exhausted native100000 at read787; specializing
existing primPure/primBind and the shared UTF8 classifier in source brought
max1024 below the unchanged bound. No evaluator optimization or budget increase
was used. Early1/31/32/33/1024 also run real stdin deliberately held open, with
exact byte stdout. Zero/early0 preserve the original state. Count decoding still
pays the complete finite allowance before the first callback.

Additional passing observations:

- Zero count with expensive initial state reaches caller marker/rejection without
  forcing it. Nonzero initial WHNF fails before marker/callback. Lazy Done R and
  final Exhausted state reach marker/rejection without demand. Unused over-budget
  Done branches remain unevaluated; hidden dormant text remains rejected.
- Continue WHNF failure after one marker write/explicit flush preserves `!` on
  real stdout; adapters report one write/one explicit flush, no success flush.
- EOF empty and after three bytes reject, no output/final flush; capacity4 short
  prefix then EOF consumes three bytes with two requests/reserved capacity8.
- Read failure after an earlier byte, partial output failure accepting one byte,
  and final-flush failure retain effects and skip later callbacks. Existing
  bridge/transport tests additionally cover nonempty read-error prefixes/poison.
- A nested3x2 loop has nine callback applications, no reads, output one byte,
  native375 steps/peak9/arena14705.
- Two independent full1024 delimiter loops: hosted reads2048/writes2/finalflush1,
  output2046; native shares100000 steps and rejects at read1139, preserving the
  first1023 output bytes, leaving909 input bytes, no final success flush
  (arena4063547). This rejection is expected budget behavior, not equivalence.
- The compact 3000-successor fold count fails the hosted entry ledger before any
  callback/read/flush; native accepts at42302steps. This tests reduction+visits,
  **not** the unresolved pre-materialization bound.
- Fifteen raw C modes cover malformed count/tag/missing payload, cyclic canonical
  count, memoized Continue/IO work exhaustion, nested pending exhaustion, mixed
  2048 ordinary bind +2048 loop frames sharing4096, arena/deep callback failure,
  zero/Done lazy payloads, and cleanup. ASan/UBSan report no diagnostics for these
  finite runs; this is not a general heap/safety proof.

Existing regressions passed: local-prefix unit executable (including raw core
count/initial usage and every-field admission checks), binary source13 tests,
native bridge14 modes, framing14 tests including **two4096-body frames** and
later-frame failure preserving earlier output. Production Frame is unchanged.

Not claimed: a completed bounded hosted decoder, verified backend/QTT
preservation, world tokens, exactly-once semantics, general exception/cancellation
safety, total-heap bounds, full parser grammar, headers, or JSON delivery.
