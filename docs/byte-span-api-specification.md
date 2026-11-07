# Bounded byte spans: specification for decision

**Design only; based on `afaf00c`. No API below exists or is approved.** This
memo refines, rather than accepts, the three-piece sketch in
[LSP workload scaling](lsp-workload-scaling.md). It recommends a smaller candidate
for review and records unresolved implementation gates. It changes no core,
primitive, runtime, admission, transport, parser cap, loop count or budget.
No larger-cap experiment, parser implementation or independent runtime execution
is claimed. The allocation/metadata audit in another lane is not assumed solved.

## 1. Recommendation and alternatives

Recommend considering **two generic pure operations**: a fixed up-to-32-byte
split, and a byte-set span returning an immutable prefix/rest pair. Reuse `Bytes`,
Bytes-specific sharing, existing Pair lowering, ordinary source variants and
`primIterateBinary` with a small explicit callback allowance. Do not introduce
`ByteExtent`, `ByteClass`, a general promotion facility or another iterator yet.
The choice of 32 bounds work between source control decisions; it is not a body,
token, header or product quota. All signatures below are proposed contracts in
binder/structural notation, **not checked `.fib` declarations**.

| Candidate | Benefit | Cost / reason not to choose it silently |
| --- | --- | --- |
| Existing operations only | No kernel surface change; suitable baseline | `primBytesIndex` constructs an octet Nat; existing slice clips and does not return the entire suffix without a count; deriving full length reintroduces unary work. Source-only alternatives are not proven impossible, only not demonstrated to fit. |
| Fixed split + 32-byte bitset span (recommended for decision) | No new runtime value kind, compact input count or effect; view pairs carry position implicitly | Two operations still need all core visitors, metered hosted/native lowering and actual source construction/composition evidence. Bitset length is rechecked on each span. |
| Small-Nat variable-width split | Width 0..32 permits finer scheduling | Extra operand decoding, zero-progress case and failure signature; no measured need over fixed width yet. |
| 256-octet 0/1 table compiler returning 32 `Bytes` | Easy source-readable classes; validate once, share existing Bytes | Optional third operation; compiler costs 256 inspections plus 32 output octets. Does not eliminate per-call bitset length checks. Source/compiler construction cost must justify it. |
| Opaque `ByteClass` | Amortized validation, potentially direct membership | New type/tag/constructors/eliminators/sharing rules and lifetime audit. Every 32-byte bitset already denotes a valid set, so opacity buys mainly caching/length evidence, not protection from invalid set contents. |
| Compact `ByteExtent` | Compact arbitrary offset/quota arithmetic | New arithmetic/failure/accounting surface. Sequential prefix/rest traversal does not need a public full-input count; no present consumer demonstrates that this additional representation is necessary. |
| Buffered iterator | Runtime could schedule blocks/quotas and demand selected fields | New effect description, admission/visitors, failure/lifetime/assignment contract. Existing loop already transports linear state/results and stops early. No concrete inability to use it has been shown. |

An opaque class or extent is not categorically wrong. Require measured repeated
validation/offset costs or an actual unexpressible consumer before paying that
surface cost. Faster lookup alone does not solve source state, token allocation,
Unicode, composition, live headers or dense JSON costs.

## 2. Read-only foundations and constraints

Inspected definitions, rather than treating proposals as implemented:

- `src/Fibril/Source/Primitive/Bytes.idr` and `Primitive.idr`: linear byte
  operands; index Missing/Found; `primBytesSlice` **clips**; `primBytesShare`
  consumes Bytes into an unrestricted box. No raw pointer or generic promotion.
- `src/Fibril/Source/Primitive/Binary.idr`, `Driver/Binary.idr` and
  `Driver/Binary/Count.idr`: `primIterateBinary` takes erased small S/R,
  unrestricted Nat and callback, linear initial state. Done/Finished is tag 0;
  Continue/Exhausted is tag 1. Count is decoded before even an immediate Done.
  Zero does not force state; nonzero callbacks receive state WHNF, not deep fields.
- `src/Fibril/Data/Bytes.idr`: hosted `Bytes` hides an immutable `List Bits8`.
  `byteLength` traverses it; slice uses `take`/`drop`. Hosted O(1) pointer-view
  metadata and O(1) length **cannot** be inferred from the native implementation.
- `runtime/native/fibril_runtime.c`: V_BYTES is pointer/length; literals are
  static, append/singletons arena-backed, slices share storage. Pair fields and
  shared boxes are lazy. `byte_work` charges ready Nat traversal as well.
- `runtime/native/fibril_bytes.{h,c}` and `fibril_binary_runtime.c`: input blocks
  survive subsequent reads until session return. Final Unit is forced before
  session teardown, then arena metadata is freed without inspecting byte views.
- `Core/Reduction{,/Work}.idr` and `Core/WeakHead.idr`: ordinary pure byte
  contractions can perform host scans inside a contraction. CountWork meters
  count-related successor visits/construction, **not general byte scanning**.
  Existing UTF-8 native conversion reserves the entire input length even on early
  malformed data; it is not an implementation of the exact-inspection policy here.

Related contracts: [foundations](protocol-foundations.md), [bytes](bytes.md),
[UTF-8](utf8-values.md), [pairs](native-pure-pairs.md),
[iteration design](bounded-binary-iteration-proposal.md),
[accepted iteration](bounded-binary-iteration.md), [binary IO](io-binary.md),
[checked IO](io-binary-source.md), [native continuation stack](binary-runtime-scalability.md),
[framing](binary-framing.md), [numbers](binary-numbers.md),
[JSON blockers](binary-json-blockers.md), [JSON adoption](json-iteration-adoption.md)
and [header blockers](header-parser-blockers.md). Historical blockers on those
pages are not reclassified as fresh observations.

## 3. Proposed signatures and exact data semantics

### Shared structural results

```text
ByteViews : Type 0 = Pair (1 prefix : Bytes) (1 rest : Bytes)
SpanResult : Type 0 = variant [
  MalformedClass (1 originalInput : Bytes),  -- positional tag 0
  Spanned       (1 views : ByteViews)       -- positional tag 1
]

primBytesSplit32 : (1 input : Bytes) -> ByteViews
primBytesSpanSet : (1 setBits : Bytes) -> (1 input : Bytes) -> SpanResult
```

`ByteViews` is a proposed source record/ordinary Sigma, both fields linear, not a
new core type. `SpanResult` is an ordinary structural variant; it does not prove
provenance of forged values. Use existing pair/record elimination and the usual
linear-scrutinee, unrestricted-consuming-branches variant eliminator pattern.
There are no erased pointer/extent witnesses. Returned fields may be shared
explicitly with `primBytesShare` if reuse is wanted. Primitive data consumption
is not deallocation or unique ownership of immutable backing storage.

**Split:** for input x, let k = min(32, |x|). Return `(x[0:k], x[k:])`.
This is deliberately an **up-to-32** operation for every input length, not an
exact split with a silently clamped caller offset. It has no width operand,
negative value, invalid width or unary length result. On empty input both views
are empty; on nonempty input k > 0. On lengths 31/32/33 it returns lengths
31+0 / 32+0 / 32+1. The entire suffix, however large, is preserved. Checking
whether the rest is empty must not traverse that suffix merely to measure it.
Native lengths suffice; hosted list shape suffices. A generic exact split would
instead need an explicit TooShort result, and is not bundled into this proposal.

**Set encoding:** a set is exactly 32 octets. For byte b in 0..255, membership is
`(setBits[b div 8] >> (b mod 8)) & 1 == 1` (low bit first). All 32-byte values
are valid, including all-zero/all-FF, NUL and invalid UTF-8. No table entry,
Unicode normalization, character range or protocol grammar is implicit.

**Span:** force/validate set length before examining input contents. If it is not
32, consume the class argument and return `MalformedClass originalInput`, with
input unchanged and **zero input-byte inspections**. The invalid class itself is
not returned. Otherwise find the maximal initial run of member octets. Return
that prefix and the exact rest as `Spanned`. A tested nonmember is charged but
**not consumed** into the prefix. Empty input succeeds with two empty views;
nonempty input whose first byte fails succeeds with empty prefix/original rest.
A 32-byte class is never rejected for bit content. No byte sentinel is used.
Tag/type errors in trusted malformed core/C fixtures, fuel, arena or evaluator
failure are runtime failures, not MalformedClass or an invented short span.

Successful split/span construction must demand input Bytes enough to produce
concrete prefix/rest values, not closures chaining prior state. MalformedClass
need not force its preserved input. This does not make existing Pair
lowering or all record fields eager. A later lowering must specify ready byte
fields and charge the wrapper/thunk allocations; source must still demand its
other retained fields explicitly. Existing box creation alone does not force a
native byte payload.

### Alternatives with fully specified failure shapes (not recommended additions)

```text
SmallSplitResult = variant [InvalidWidth Bytes, Split ByteViews]
-- Same linear payload convention as SpanResult.
splitAtMost32 : (1 width : Nat) -> (1 input : Bytes) -> SmallSplitResult
-- canonical width 0..32: prefix min(width, |input|), exact rest;
-- canonical width >32: InvalidWidth original input, never clamp to32;
-- width0: two views (empty, input), no progress;
-- noncanonical/malformed/cyclic operand: charged runtime failure, not data.

ClassCompileResult = variant [MalformedTable, Compiled (1 setBits : Bytes)]
compileByteSet : (1 flags : Bytes) -> ClassCompileResult
-- valid iff exactly256 octets, each0 or1; output exactly32 bytes in above order.
-- invalid length or value consumes flags, yields no usable set; no coercion
-- of 2/255 to true, no truncation/padding, no generic class Type or promotion.
```

The variable-width alternative above promises canonical whole-Nat validation,
so it must charge every tail and bound cycles, even when width is already known
to exceed32. Short-circuiting at a witnessed 33rd Succ without inspecting the
unused tail would be a different demand contract, not this signature's promised
failure behavior. That added decoding cost is another reason to prefer no width
operand. Neither alternative authorizes a new primitive now.

### Constructibility, not just representability

UTF-8 encoding cannot generate every octet: FF/FE and C0/C1, for example, never
occur in valid UTF-8. Slicing valid encoded text does not fix that. Do not propose
"encode the 32-byte string" as a general bitset constructor. Scalar U+0000 is
valid in conversion, but source literal/control policy and console NUL rejection
are separate. `primBytesOctetMod256 Zero` constructs a NUL byte without text.

Existing singleton modulo construction with canonical n in 0..255 can construct
**every** table octet, followed by append and BytesShare. This is a constructive
finite method, not a cheapness/admission claim: repeated unary constants, append
copies, transparent helpers and class setup may dominate closed core syntax.
An offline source generator can emit those existing expressions (not a runtime
protocol parser); checked-core/native literal injection alone is not evidence
that arbitrary bitsets fit checked source. Measure actual shared source classes
(whitespace, digit, safe string byte, token-name classes) and a worst-shaped
arbitrary class before approving a constructor convenience. The optional compiler
could accept an ASCII `'0'`/`'1'` encoding instead, but that would be a *different*
contract from the binary0/1 proposal and must not be silently substituted.

A compiler returning Bytes solves reuse without a new class Type: share its
successful payload once, extract the unrestricted Bytes field, and pass it once
per span application. All fallible branches must be handled. No caller may
unwrap a malformed table/failed UTF8 conversion as an empty valid class/string.

## 4. Existing iteration is the first scheduling candidate

No full-input Nat length is needed. State carries buffered rest, a current block
remainder, grammar/UTF-8 state, raw token fragments, source quota state and any
explicit retained result. The callback is unrestricted and cannot capture linear
ambient payloads; they travel inside its linear state. Reusable bitsets may be
captured via existing BytesShare. The result type can differ from the state.

```text
-- Fibril source pseudocode, not checked code; helpers below are SOURCE code.
step : (1 state : Scan) -> IO (LoopStep Scan Reply)
step state =
  eliminate state into (blockRest, outerRest, grammar, fragments, quota)
  if blockRest empty:
    if outerRest empty:
      Done (sourceFinalize grammar fragments)   -- no IO/refill; whole-body gate
    else:
      (block, outerRest') = primBytesSplit32 outerRest
      -- Source assigns this block only if its explicit quota allows it.
      -- Keep block + outerRest' on refusal; do not drop buffered suffix.
      sourceProcess block outerRest' grammar fragments quota
  else:
    sourceProcess blockRest outerRest grammar fragments quota

primIterateBinary Scan Reply smallAllowance step initial
-- Finished Reply or Exhausted Scan; caller consumes BOTH outcomes explicitly.
```

`smallAllowance` is a source-selected small canonical/compactly constructed
constant, not `primBytesLength body` or an implicit4096. Scheduling is one source
control quantum per callback: it may consume a long safe span, one escape/number
transition, or finalize. No claim that exactly one callback handles every
32-byte block, nor that128/129 callbacks handle every4096-byte JSON body.
Empty input with zero allowance returns Exhausted without invoking the finalizer;
nonzero allowance can finalize it as InvalidJSON. Final Continue at allowance
zero returns state without forcing its fields, per existing loop semantics.

A span can return zero on nonempty input. The callback must then classify and
consume a delimiter/escape byte, change grammar mode with a bounded control
transition, finish, or reject. Repeating the same empty span without progress
must spend allowance/work and eventually exhaust, never spin outside accounting.
Repeated rescanning spends work again. Input exhaustion, allowance exhaustion,
quota refusal, malformed class, invalid syntax and runtime failure stay distinct.
No exhausted state becomes a successful partial parse or a new default token cap.

**Early Done:** the existing iterator assigns no bytes itself. If source assigned
a32-byte block and recognized a stopping point after7, Done must retain the25
unexamined block bytes **and** all outer rest, in order, in its Reply. Assigned
byte quota (if the caller chose that policy) charges32; logical parsed bytes are7;
class-test inspections can include a preserved failing byte. These are different
counters. A source quota may instead charge parsed bytes, but then source must
explicitly carry/decrement it and cannot call that the assignment policy. The
recommended cost experiment should use assignment charging, once per fresh
block, not again when revisiting its retained remainder. For whole JSON success,
no unexamined body suffix is allowed. Early invalid data may preserve the suffix
in the result or consume it by an explicitly documented source rejection contract;
it cannot claim that suffix validated. Outer transport consumption already
happened when the body was read; returning a view does not rewind stdin.

Before proposing another iterator, construct this source composition and show a
specific failure attributable to scheduling/field demand that cannot be resolved
with the existing loop and ready byte results under the same policy. A measured
callback/metadata cost can justify reconsideration; a conceptual desire for blocks
is not proof of inability. Nested existing loops never renew native work/arena or
transport quotas. No new exhaustion/quota semantics are hidden in a wrapper.

## 5. Source grammar across boundaries, not runtime parser opcodes

Generic spans do not validate UTF-8, JSON, decimal Content-Length or headers.
All grammar/state machines stay in Fibril. Pseudocode continuation obligations:

```text
sourceProcess block outer grammar fragments quota:
  case grammar.mode:
    whitespace:
      (white, rest) <- span whitespaceSet block
      retain/account white; sourceGrammarDispatch rest outer
    stringPlain:
      (safe, rest) <- span safeStringByteSet block
      sourceUTF8Advance carriedUTF8 safe   -- do not decode each block separately
      retain raw fragment safe
      if rest empty: Continue (StringPlain carriedUTF8, outer)
      else: sourceConsumeQuoteBackslashOrRejectControl rest outer
    escape:
      sourceConsumeOneEscapeOrStartFourHexDigitsAcrossBlocks
    unicodeEscape:
      sourceAccumulateExactlyFourHex; carry pendingHighSurrogate
      requireLowSurrogateEscapeAfterHigh; rejectLoneLowOrUnpairedHigh
    number:
      sourceNumberDFA sign/int/fraction/exponent across block boundaries
      -- leading-zero, digit-after-dot/exponent/sign requirements; no host float
      -- terminating delimiter stays unconsumed until grammar dispatch
    literalOrStructure:
      sourceMatchTrueFalseNullOrPunctuation; update complete nesting state
  -- empty block is not EOF; continuation carries partial UTF8/escape/number state

sourceFinalize:
  require full declared body supplied and no current/outer suffix
  require UTF8 accepting state (no truncated/overlong/surrogate/out-of-range scalar)
  finalize only complete number/literal, closed string and balanced containers
  require exactly one top-level value followed ONLY by JSON whitespace
  validate every object key/value, preserving order and duplicates
  return raw tokens only after these gates; envelope projection/dispatch is later
```

A safe string-byte class may contain high octets for batching, but membership
alone is not Unicode validity; carry continuation/minimum/scalar state or perform
a separate strict whole-buffer UTF8 conversion before scanning. Whole-buffer
validation is an additional charged pass, not free, and a large pure conversion
has its own existing hosted accounting limitation. Raw bytes below20(hex),
including00, are forbidden inside JSON strings; `"\u0000"` decodes to valid scalar
NUL. Backslash/quote exclusion and UTF8 state must not be weakened for spans.
Escaped surrogate pairs may cross any boundary; invalid overwritten duplicate
values must reject even if a later key/value would replace them in a map. Compare
keys only after decoding when a later semantic duplicate policy requires it;
raw `"id"` and `"\u0069d"` have equal decoded spelling. Do not choose last-wins,
first-wins or envelope ambiguity policy as part of the byte API.

Number DFA must distinguish `0`, `-0`, fractions, exponents and incomplete tokens;
keep exact raw lexemes until a separate bounded numeric/id conversion. Reject
trailing garbage or second top-level values, including after a syntactically
valid first value. Depth, byte and token admission/refusal must remain distinct
from malformed syntax. No new product limits are chosen here.

Current diagnostic tokens are **raw quoted string / number lexemes**, not decoded
strings, AST nodes or typed events. A real decoder must unescape, combine valid
surrogate pairs into scalar UTF8, preserve scalar NUL/noncharacters, bound/charge
output storage and identify ID kinds (absent/null/string/number) explicitly.
UTF-16 edit coordinates need their own source conversion. A serializer must quote
and escape decoded keys/strings, controls/NUL/quote/backslash, emit scalar UTF8,
validate numeric policy and compute **encoded byte** Content-Length. No raw
lexeme echo or initialize-success marker is a valid substitute for those gates.

Every `span` pseudocode call above must eliminate `SpanResult`: Spanned transfers
both views; MalformedClass returns a distinct source configuration failure with
its original input, never InvalidJSON or an empty successful match. Quote,
backslash and structural boundaries additionally require an accepting raw UTF8
state; an unfinished multibyte sequence cannot be terminated by ASCII syntax.
All abbreviated Continue states retain grammar, fragments, quota and both suffix
fields; no pseudocode branch grants linear discard.

For headers source still owns strict CRLF across splits, token names, case
comparison without lowercasing values, length-field uniqueness, decimal lexical
bounds/overflow and any separately approved optional-header policy. The current
`echoFrame : IO Unit` is an opaque echo, **not** `withFrame`/a body-handler API.
This memo cannot compose an unavailable validated-body callback into a server.

## 6. Lifetime, allocation and IO contract

Views are immutable and backed by original static, arena or session storage.
Native prefix/rest results must retain that backing lifetime through later reads,
callbacks, Done and Exhausted consumers. Never point into reusable scratch data,
callback stack objects or prematurely freed chunks; do not flatten nested views
by copying unless explicitly charged. Empty views need no dereferenceable pointer.
Hosted list prefixes may allocate at most their traversed length, suffixes can
share tails; this is not native O(1) metadata nor a packed-array redesign. A tiny
native view can pin the whole session input buffer. No early reclamation, cross-
session escape, owned promotion or new destructor is approved. Failure cleanup
must preserve existing session-before-arena teardown without inspecting freed
views. Count headers, values, thunks, closures, retained backing storage and copied
prefixes separately from arena payload. The other audit may refine evidence; it
cannot be assumed to eliminate these costs.

These operations perform **zero reads/writes/flushes/reservations**. Empty buffered
input is data, not physical EOF. There is no implicit refill/read-until, rollback,
drain or raw-descriptor handoff. Existing `primReadBytes` fills capacity or stops
at EOF/error; short prefixes and poison retain their current meanings. A short
complete header with stdin still open can block a wide fill-capacity read waiting
for body/next-message bytes. Generic buffered spans do not solve generalized live
headers. No overread, read-some or read-until policy is approved here. Existing
canonical framing remains unchanged, including body4096 and explicit flushes.

## 7. Accounting contract and unresolved hosted gate

For a valid class and input length n with maximal matching prefix k, define
`I = k + (if k < n then 1 else 0)`. Empty input has I=0; first-byte failure I=1;
all-member input I=n. **Charge each of these I membership inspections**, including
the preserved nonmember. Proposed portable validation charge is
`V = 1 + min(classLength, 33)` work units: one entry check plus one per observed
class cell, stopping on an excess-length witness. Thus valid32 costs33, empty
costs1, length31 costs32, and every length >=33 costs34. Hosted performs bounded
list traversal; native can use length metadata but reserves the same logical V
before scanning. This conservative cross-backend charge is distinct from actual
memory accesses and from I, and does not require constructing a length Nat.
The offline model reports I only; it does not implement or validate fuel debits.

Each membership test's class-byte lookup also has a representation cost. If
hosted lookup walks list cells, charge each access too (at most32 per test), on
top of I. Alternatively materialize a32-entry host lookup cache during validation
and charge its storage/setup explicitly; native may retain the original storage.
That cache choice and its exact allocation schedule remain approval obligations,
not a new public class type. Do not advertise one physical access per byte on the
current hosted list or omit these costs from predicted performance.

Split has no octet-content tests: native target is O(1) metadata; hosted must
traverse/copy up to32 prefix cells and inspect the terminal shape. Charge that
traversal/copy and all view/pair/result/thunk metadata separately. An optional
compiler charges every inspected entry, validity check and output byte. Invalid
input can fail early, but each inspection performed still spends work. Length
validation must stop after a bounded witness to excess, not scan a huge invalid
table to compute full length. No large unary Nat construction is allowed as a
hidden preliminary length test. Repeated class validation and scans are charged
again; any actual memoization may avoid repeated work, not invent a refund.

Native per-byte work must debit the **existing global100000** steps before each
inspection (or a safely reserved bound); memory debits existing16MiB arena before
allocation. No uncharged O(n) C helper under a single evaluator step. Account
source wrapper reduction, ready byte fields, callback/application, pending-frame
scheduling, bounds/empty checks, class setup and finalization in addition to I.
Per-class fixed charges and actual allocations need exact lowering numbers in
a future cost report; they are not measured by this memo.

**Blocking design obligation:** ordinary hosted pure reduction currently has no
general byte-work debit path. Adding a pure O(n) scan as one contraction would
violate this specification. Before code approval, specify how full/head reduction,
normalization, guarded conversion and nested CountWork paths reserve/debit all
inspection/traversal work **before doing it**, propagating the same remaining
ledger through nested evaluation. Specify fuel exhaustion separately from data
failure, including denial before result allocation. The existing Identity policy
cannot be cited as a metered scan implementation. If meeting this requires a
reducer/accounting change, seek explicit approval; do not silently broaden this
task or claim metering already exists. A different explicitly effectful operation
would also need a separately approved capability/signature design.

No artificial per-block work reset is allowed. Hosted existing per-call fuel4096
and description-depth4096 remain different scopes from native session-global
steps; they are **not** a common numeric budget. A future design must state which
hosted ledger owns scan work across calls, expose cumulative measurements and
retain existing scopes, or obtain approval for any new session-wide policy. It
may not mint a fresh "full parser budget" per block/nested loop. This unresolved
integration is a reason to stop before implementation, not a license to use an
unmetered host helper. Transport request/capacity remains session-wide: CLI4096
requests /8MiB reserved capacity; raw transport admission allows100000 requests,
65536 per chunk. No buffered operation spends/refunds these reservations.

## 8. Feasibility and admission: no claimed solved workload

- A raw count derived from length4096 costs **2n+2 = 8194 >4096** hosted count
  units before callbacks; source wrappers cost more. Never derive full-input Nat
  to schedule scanning. Small constant allowances remove that particular trap,
  not all4096-byte or token-dense parsing costs.
- The existing64-token/64-byte native JSON diagnostic costs **97768 steps** and
  **2998705 arena payload bytes** (about3MB). The3681-byte initialize has720
  lexical tokens. Long-string spans and cheap membership do not demonstrate
  feasibility of those per-token grammar/allocation costs. Do not multiply small
  profiles and report the projection as execution, or select512 tokens silently.
- Even assigning32-byte blocks over4096 needs128 assignments, but escapes,
  punctuation, zero spans, UTF8 state and finalization add source work/callbacks.
  At100000/4096 only24.4 steps/byte are available before fixed costs. This is a
  yardstick, not a promised fit. One full scan already costs at least4096 byte
  inspections; UTF8 prevalidation adds another pass, plus validation/setup.
- Actual closed typed-core composition must include byte helpers/classes,
  framer/body handoff (if separately made available), source JSON finalizer,
  decoded-value/envelope projection, typed lifecycle consumer and serializer.
  Check **8192 initial nodes,8192 literal payload units,200000 construction**
  before any effects; checking depth512/type reduction128 and native depth512 /
  pending4096 remain unchanged. Track lexical sharing, transparent wrappers,
  erased annotations and dormant branches. Read65 is8002 nodes; JSON API7467;
  framer4341. Neither their sum nor each isolated fit proves the actual entry.
  The full-ID four-event lifecycle handshake already fails at8467 nodes.
- Whole-syntax capability/resource admission cannot be bypassed by new pure
  result records, erased class annotations or dormant callbacks. Pure byte ops
  grant no IO; existing iteration remains binary-only even with pure callbacks.
  No opcode for JSON/header parsing, new cap or budget exemption is permitted.

## 9. Future acceptance matrix (requires separate implementation permission)

Every source row must check and run genuinely hosted and emitted native at the
unchanged limits; separately label raw trusted fixtures and sanitizer scope.
Record exact output/data tags, suffix bytes, callbacks, assigned/parsed/inspected
counts, logical IO consumption/prefix failures, requests/capacity, native global
steps/depth/arena/allocation counts, hosted scan ledger and closed node/payload/
construction metrics. Timeouts, fuel denials and reader cap denials are **not**
whole-parser successes. No C/Python protocol parser may replace Fibril source.

| Matrix | Required cases and assertions |
| --- | --- |
| Octets / classes | All256 octets as member/nonmember, including00/80/FE/FF; every singleton bitset and complement, empty/full sets, bit order at7/8/127/128/255, arbitrary32-byte sets; source construction (not just raw literals). |
| Invalid class / optional compiler | Class lengths0..31/33/256 and very large invalid class: distinct MalformedClass, original input intact, I=0, bounded length-witness work; optional flags length255/256/257 and every non0/1 byte at every position, no class on failure; fuel/arena errors remain runtime errors. |
| Split / maximal span | Input lengths0/1/31/32/33/63/64/65 and4095/4096/4097; prefix+rest identity, maximality, first failing byte preserved/charged, all-match/zero-match/empty; nested views and repeated rescans; no whole-input unary length. Variable-width alternative, only if chosen:0/1/31/32/33, TooShort for any exact variant, malformed/cyclic trusted counts. |
| Loop / progress / suffix | Allowance0, early Done before processing and inside assigned block, Continue then Exhausted, empty buffer, repeated zero-span control, invalid byte first/middle/last; return in-block suffix before outer suffix, no extra callback/read/refill, explicit quota refusal and finalization callback. Distinct S/R payloads; retained fields demanded without deep-strictness claim. |
| Lifetime / failures | Retain static, append-arena and session views through distinct later reads (mutated scratch negative control), nested callbacks, Done/Exhausted, later rejection and consumer demand; ASan/UBSan no UAF/double free on represented paths. Read/write/explicit/final-flush failure preserves prefixes/poison and skips later work/success flush; cleanup counters distinguish arena/session storage. |
| Unicode / JSON | Every UTF8 continuation/escape/four-hex/surrogate/CRLF/number split around31/32/33 and4095/4096/4097; overlong, truncated, lone surrogate and >10FFFF; scalar NUL conversion vs raw JSON control vs escapedNUL; quote/backslash/control escapes and decoded serializer round trips, Unicode byte-length framing. Numbers leading zero, signs, fractions/exponents, delimiter retention, partial tokens; nesting and all duplicate values including overwritten invalid Unicode; trailing garbage/second root, complete-body gate. |
| Resources / admission | Per-inspection fuel denial at failing-byte boundary, repeated/nested scans/loops share required work scope, arena/pending failure after earlier effects; whole-syntax hidden text/file/reference rejection including erased/dormant positions before IO; source rejection of linear capture/duplicate/drop and mismatched variants; actual composed entry construction/node/payload gates. |
| Workload | Preserve all current64-byte oracle cases first; after explicit larger-experiment approval, dense720-token initialize, escape-dense/control/long key strings, whitespace and4k body boundaries, Unicode document messages and two-frame suffix isolation. Require complete-body examination/exact expected fields and serializer output, not opaque echo or Read65 denial. No universal limit claim from samples. |
| Live framing regression | Existing canonical framer still completes on fragmented complete input with stdin open, two max4096 bodies, early oversize refusal; generalized short complete header + open stdin remains explicitly blocked for wide fill-capacity reads until a separate transport decision. |

`tools/test_byte_span_contract.py` is an **offline contract algebra model only**:
it checks split/span conservation, bit order, malformed-length behavior and the I
formula over byte vectors. It is neither a parser nor Fibril/runtime execution,
source constructibility proof, allocation/lifetime test, metering implementation
or independent implementation differential. No production library build is
needed for this specification. Historical profile numbers above are read-only
evidence; this task does not rerun them.

### Validation performed for this specification

- `python3 tools/test_byte_span_contract.py -v`: seven offline model tests pass.
- `python3 tools/test_json_oracle.py`: eight existing offline oracle tests pass.
- `python3 tools/generate_lsp_workload.py --check`:14 existing bodies/frames verify.
- Local checks pass for all memo links, unique handbook registration, the proposal
  follow-up link and model Python syntax; Pandoc GFM rendering passes with warnings
  treated as errors, output only in `build/byte-span-spec/`.
- `git diff --check` passes. No Fibril/compiler/library build, full handbook suite,
  new protocol execution, profile, sanitizer or independent runtime check is
  claimed. Existing oracle/generator checks do not validate proposed operations.

## 10. Decision boundary / open questions

Recommended minimal proposal is fixed split32 +32-byte Bytes bitset span using
existing Pair/BytesShare/iteration, **conditional on** a metered hosted design and
actual class construction/closed-composition evidence. Keep optional class
compiler, variable widths, opaque types and buffered iterator out unless evidence
justifies them. Remaining parent decisions before implementation approval:

1. Accept/reject this two-operation contract, including invalid-class input
   preservation, explicit up-to split semantics and source-assigned quota policy.
2. Approve a specific metered reduction integration and precise validation/cache/
   metadata charging schedule; no current path satisfies that requirement by
   assumption. Decide whether pure signatures remain suitable if the metering
   integration cannot preserve existing boundaries.
3. Decide whether measured source class construction warrants the optional256
   flags compiler; do not introduce an opaque Type merely to make Bytes reusable.
4. Authorize any later source cost spike/large workload experiments separately;
   none is performed here. Resolve live-header transport, body-handler API,
   decoded strings/serializer and actual typed composition in their own scopes.

**Stop here for parent review/approval. No implementation or new runtime claim.**
