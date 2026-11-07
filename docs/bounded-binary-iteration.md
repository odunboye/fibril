# Bounded binary iteration — implementation and count-safety follow-up

Status: **independently reviewed and accepted on the isolated foundations branch**.
The typing/admission/runtime audit found no observed bug. Its P2 coverage gap
(prior source tests used S=R=Bytes; sanitized raw loops used Unit without reads)
was closed by the distinct-payload/session-view tests and independent follow-up
review. Reviewed production code is unchanged by that test-only follow-up.
The earlier d6e034b checkpoint was partial: ordinary head reduction could allocate
unary naturals before the count ledger charged their visits. The follow-up closes
that specific gap with a shared policy-parametric reducer, not a second evaluator
or a top-level preguard. Parent acceptance validation is recorded below.

`Core/Reduction/Work.idr` provides an unmetered Identity policy and a bounded
CountWork policy. Existing `step`/`stepHead` select Identity; count entry selects
CountWork. Both reducers carry the policy through **all** recursive calls,
including head-to-full operand fallbacks. Neither bounded path calls ordinary
`step`, `stepHead`, `canonicalNatural`, `canonicalOctet`, or the old byte-contract
helpers. BytesLength and BytesIndex's octet payload are the two contractions
that materialize unary naturals from host Nat metadata; both now call the policy's
`materializeNatural`.

`reserveNatural amount build` checks/subtracts amount from the remaining ledger
**before calling build**. The total `reserveNaturalDenied` theorem proves denial
for an arbitrary builder, so rejection does not require constructing the natural
first. A separate closed test theorem instantiates that result with
`naturalTerm 1000000` and work4096. This is structural preallocation evidence,
not an inference from eventual failure or RSS measurements.

The ledger bounds count-entry canonical-successor traversal and newly
materialized unary Term successors from those contractions. It does **not** bound
every pre-existing byte allocation, byte-length scan, substitution/copy, arbitrary
primitive CPU work, allocator overhead, or total heap. Generic pure evaluation,
state/result WHNF, and effects outside count entry retain their existing budgets.
No generic natRec demand rule, native runtime limit, or separate count cap changed.

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

Hosted `Driver/Binary/Count.idr:decodeBinaryCount` initializes one ledger from
caller fuel4096. Each outer successor visit or head contraction consumes one unit;
terminal inspection requires one unit. The policy threads the **same remainder**
through nested reduction, full-step fallbacks, primitive canonical Nat/octet reads,
and unary construction. Full-step successor inspection and NatRec/Runtime
successor matching also spend a unit per visit. A materialized n-successor natural
reserves n units before construction; later visits still spend their own units.
Exhaustion is distinct from irreducible/noncanonical input: outer CountWork
Nothing means exhaustion; a successful policy result containing Nothing is stuck.

For a raw `BytesLength (BytesValue bytes)` with n octets the complete count decode
cost is **2n+2** (one contraction, n construction, n visits, one terminal).
A canonical unary n costs n+1. Beta or an outer successor adds one. The tested
identity NatRec fold over that byte length costs6n+3, including scrutinee visits,
its contractions and the produced count's visits. A selected BytesIndex octet q
at canonical index0 costs2q+4 including its variant-case/beta elimination.
These are decoder costs, not source-wrapper costs: source beta/UTF8/byte operations
spend additional work. Consequently direct length1024 needs2050 and succeeds;
source length2048 cannot fit4096. That is a ledger boundary, not a new count cap.

Original compact source is checked before decoding; no recursive recheck of a
materialized1024 Nat is introduced. Ordinary state/action/result weakHead calls
still receive existing per-call fuel independently of the count-entry ledger.
The driver decoder is covering because its policy-returned remainder is opaque
to structural termination checking; the actual policy operations never increase
that remainder and each outer recursion consumes work. This is not a new formal
termination or total-heap theorem.

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
make -j8 binary-count-test IDRIS2=/path/to/pinned/idris2
make -j8 binary-iteration-test IDRIS2=/path/to/pinned/idris2
```

The bounded foreground iteration run passes **11 test groups**, including checked source
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
  as well as the newly charged materialization; hosted/native budgets differ.
- Fifteen raw C modes cover malformed count/tag/missing payload, cyclic canonical
  count, memoized Continue/IO work exhaustion, nested pending exhaustion, mixed
  2048 ordinary bind +2048 loop frames sharing4096, arena/deep callback failure,
  zero/Done lazy payloads, and cleanup. ASan/UBSan report no diagnostics for these
  finite runs; this is not a general heap/safety proof.

Existing regressions passed: local-prefix unit executable (including raw core
count/initial usage and every-field admission checks), binary source13 tests,
native bridge14 modes, framing14 tests including **two4096-body frames** and
later-frame failure preserving earlier output. Production Frame is unchanged.

## Count-safety focused evidence

`Tests.BinaryCount` adds22 raw-core/policy checks plus the closed denial theorem.
They cover the exact boundaries above, zero/tiny/1024 values, beta/successor/NatRec
nesting, construction of the BytesIndex255 payload, demanded full-step/octet
fallbacks, computed byte operands, exhaustion versus noncanonical input, and
unused branch/argument laziness. These are trusted raw syntax tests, not source
provenance claims. Existing generic root-step/Fuel proof statements are unchanged
and still check; no holes, unsafe casts or totality assertions were introduced.

`tools/test_binary_count.py` runs the22 core checks separately and adds four
**checked-source** groups using the same
private .ipkg harness as the iteration suite. Direct5000-byte lengths and lengths
hidden under beta, successor, NatRec, computed append, full octet/index/slice/length-comparison operands all reject hosted before callback effects: reads0/writes0/flushes0,
input untouched. Their original compact source checks and emits native C; native
can decode the larger finite counts under its different budget. Zero, small,
1024 and index-produced counts behave as expected. Unused5000-byte count branches
and erased beta arguments do not materialize. The source length2048 case
explicitly distinguishes construction+visits from the old visit-only accounting;
it is not a required parser limit or a new count cap.

The full local-prefix unit/property suite passes, including ordinary full/head
reduction, byte-range, UTF8 codec, typing and usage checks. The iteration suite
now has13 groups, including max1024, the distinct-type source fixture,15 original
raw native modes and9 read-backed lifetime modes. Those raw fixtures and the
new distinct-payload checked-source fixture run normally and under ASan/UBSan.
At that worker checkpoint, other checked-source fixtures including max1024 used
ordinary native compilation; no sanitizer coverage is claimed for those earlier
builds. The later parent run explicitly enabled sanitizers through CC (below). The count suite remains5 groups (22 core checks plus
four checked-source groups). No production source changed in the payload/lifetime
follow-up; the full unit/source/framing runs above describe the count-policy
checkpoint and are not claimed as newly rerun for this test-only change.

## Distinct state/result payload and session-view lifetime coverage

`tools/fixtures/binary-iteration/views/Main.fib` is genuinely checked source with
S=`Phase` and R=`Reply`, not differently named Bytes aliases. Phase has three
nominal variant arms (Begin0/Middle1/End2), Reply has one (Answer0), and both carry
another nominal variant, Fragment (Spare0/View1), with a linear Bytes payload.
The one-arm Reply uses its declared eliminator, `useReply`. Swapping the Finished
and Exhausted handlers is rejected by source checking. All state/result payloads
are consumed linearly. The initial slice uses the EXISTING Bytes-specific
`primBytesShare`/SharedSlice U permission, followed by `primBytesLengthIs`
(expected length5) on its
Bytes field BEFORE starting the loop. Sharing alone would leave native payloads
lazy; the guard demands the slice itself and the same shared field is then used
once for state transfer. A four-byte slice negative control rejects after the
initial read, with zero callbacks/extra reads/writes/flushes. No new sharing or
generic promotion/discard facility is introduced. This is not a claim of globally
linear Bytes ownership or source-level pointer identity.

The program reads8 octets `7e 00 ff c3 28 80 fe 7f`, slices offset1/length5, and
retains `00 ff c3 28 80` through two Continue transitions and additional reads.
The bytes include NUL, FF and malformed UTF8, and are never decoded. Three
callbacks read the following `61 62 63` and Done transfers the slice through the
different Reply type. A short allowance2 instead returns Exhausted Phase.End;
its consumer extracts the same slice. Prefix D/E distinguishes the two routes.
Pure source helpers are locally shared to remain under the unchanged admission
limit; the initial transparent-helper draft exceeded8192 nodes and was simplified,
not admitted by raising a limit.

| Checked-source case | Allowance / callbacks | Read requests / consumed input | Exact stdout hex | Reserved requests / capacity | Core nodes | Native steps / peak / arena payload |
| --- | --- | --- | --- | --- | --- | --- |
| Done | 5 / 3 | 4 / 11 | `44 00 ff c3 28 80` | 5 / 17 | 7529 | 816 / 20 / 31606 |
| Exhausted | 2 / 2 | 3 / 10, one byte unread | `45 00 ff c3 28 80` | 4 / 16 | 7496 | 662 / 17 / 25702 |

Both cases have one write and one success final flush. They run through hosted
source execution and genuinely emitted native C, with exact binary stdin/stdout
comparisons, plus adapter counters/output checks. Emitted native also runs under
ASan/UBSan, both with adapters and real stdin/stdout. Caps are unchanged:
8192 core nodes, hosted depth/fuel4096, requests4096/capacity8388608, native
100000 steps/512 pure depth/16MiB arena/shared4096 pending. The allowance5 Done case
must not execute the two remaining callbacks.

`ViewLifetime.c` is separately labelled **trusted FEval injection**, not source
typing evidence. It takes the first chunk through the real binary transport,
uses `f_bytes_slice`, and asserts the retained view pointer equals that session
chunk's data+1 (not an arena/static copy) on every callback and consumption.
Nested Phase/Fragment and Reply/Fragment payloads retain it while further reads
allocate new session blocks. An early marker write+explicit flush makes later
failure effects observable. Its9 normal and ASan/UBSan modes cover:

| Trusted mode | Callbacks / read requests / consumed bytes | Write requests / accepted bytes | Flush calls |
| --- | --- | --- | --- |
| Done success | 3 / 4 / 11 | 2 / 6 | 2 (explicit + final) |
| Exhausted success | 2 / 3 / 10 | 2 / 6 | 2 |
| Callback rejection after marker | 3 / 4 / 11 | 1 / 1 | 1, no final flush |
| Done consumer rejection after retained-view write | 3 / 4 / 11 | 2 / 6 | 1, no final flush |
| Exhausted consumer rejection after retained-view write | 2 / 3 / 10 | 2 / 6 | 1, no final flush |
| Physical read failure with consumed prefix1 | 3 / 4 / 11 | 1 / 1 | 1 |
| Physical view-write failure accepting prefix2 | 3 / 4 / 11 | 2 / 3 (marker + prefix) | 1 |
| Final-flush failure | 3 / 4 / 11 | 2 / 6 | 2 (second fails) |
| First explicit-flush failure | 1 / 1 / 8 | 1 / 1 | 1 |

Every physical-failure case before final flush verifies poison prevents further
adapter reads/writes/flushes. Each mode asserts exact callbacks, payload bytes,
read/write prefixes where applicable, no rollback, and no successful final flush
on rejection/failure. Test-only malloc/free counters prove session blocks have
been released before only arena metadata is walked; after arena teardown, tracked
live allocations are zero and releases equal allocations. ASan/UBSan report no
UAF/double-free diagnostics in these scenarios. This does not establish arbitrary
runtime payload types from erased S/R, universal lifetime safety or total heap
bounds. No concrete production bug was observed by these added tests.

Reproduce just the new coverage using the pinned/private-staged environment:

```sh
IDRIS2=/path/to/pinned/idris2 python3 tools/test_binary_iteration.py \
  BinaryIteration.test_distinct_state_result_nested_variants_retain_read_slice \
  BinaryIteration.test_native_read_backed_view_lifetimes_and_failure_cleanup -v
make -j8 binary-iteration-test IDRIS2=/path/to/pinned/idris2
```

## Parent acceptance on the foundations branch

Independent reviews accepted the count/reducer refactor and the complementary
source-typing/admission/native-runtime portion. The later coverage review closed
the distinct-payload/session-view finding; its remaining documentation correction
now names sanitizer subsets rather than claiming every prior native build was
sanitized. No production defect was found by those reviews.

The parent then ran the combined `make -j8 test editor-test handbook` gate on the
integrated code with the pinned compiler and private package staging. It passed
the unit/property phase, 163 CLI, 19 native-emitter, 8 pair, 7 byte/codec native,
13 binary-source, 14 bridge scenarios in one test, 5 count, 13 iteration,
9 scalability, 6 number-probe, 8 oracle, 14 framing, 9 interactive CLI, 7 editor
and 16 handbook tests. Separate hosted IO compatibility passed315 checks.

A separate parent invocation set `CC='cc -fsanitize=address,undefined
-fno-omit-frame-pointer'` for count/iteration and console/resource/binary-transport
targets. The count5/iteration13, console-native19, resource-native25 and
transport19 tests passed; checked resource hosted/native differentials also
passed. The iteration source builder honors this CC, so this later run includes
sanitized checked-source max1024 as well as the raw and distinct-payload suites.
This extends earlier coverage without reclassifying earlier ordinary builds.

The 97-case combined JSON diagnostic was repeated after the shared reducer
refactor: hosted70 matches/26 budget blockers/1 reader EOF, native93 matches/
3 blockers/1 EOF, no mismatch/unexpected failure/deadline. These blockers are
not successful parser executions. Neither generalized headers nor 4096-byte
JSON has been delivered by the iteration mechanism.

No runtime limits were raised. Main, LSP and the canonical Frame source remain
unchanged. Integration is confined to `feature/protocol-foundations`.

Not claimed: verified backend/QTT preservation, world tokens, exactly-once semantics, general exception/
cancellation safety, total-heap or general CPU bounds, full parser grammar,
headers, or JSON delivery.
