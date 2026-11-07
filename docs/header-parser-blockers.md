# Header parser investigation: stopped, no production extension

The newer [accepted-iteration adoption attempt](#accepted-iteration-adoption-checkpoint)
also stopped at a measured diagnostic: native classification/state work still
blocks the requested 1024-byte header. The following original investigation is
historical; the accepted iteration primitive itself is now implemented.

This is an **evidence-only checkpoint**, not a generalized header implementation.
The supervisor stopped this path after the 1024-transition prototype failed the
unchanged execution budgets. `examples/modules/binary-frame/Protocol/Frame.fib`
is restored byte-for-byte to baseline `0efe064`. Its canonical grammar, body cap
4096, `echoFrame`, one-/two-frame clients and transport accounting are unchanged.
No production `withFrame` API, optional fields, case-insensitive headers or new
header caps are delivered. [Binary framing](binary-framing.md) remains the
production contract. No core/runtime/primitive or JSON-lane files changed.

The intended integration seam was
`withFrame : (onBody : (1 body : Bytes) -> IO Unit) -> IO Unit`, with an
unrestricted callback and linear validated opaque body. It is **not available**.
The private header-aware callback in the abandoned construction fixture is not
an exported integration interface. There is no full-LSP-compliance claim.

## Diagnostic fixtures

`tools/fixtures/header-loop/` is deliberately outside the production examples
and test registration. All parsing/classification/looping is Fibril source;
`tools/probe_header_loops.py` only invokes processes and observes their output.
The probe does not assert that today's failures must remain failures.

- `flat32/Main.fib`: minimal running continuation-transport experiment.
- `nested32x32/Main.fib`: the same transition in 32 blocks of 32, **1024 total**
  transitions, not a reset allowance of 1024 per block.
- `flat1024/Main.fib`: the same transition with a flat 1024-deep Nat count.
- `drain1024/Main.fib` and `drain1024-constant/Main.fib`: later no-read state
  forwarding minimization/control, observed by `tools/probe_header_loop_depth.py`.
  See the [bounded iteration proposal](bounded-binary-iteration-proposal.md) for
  measured alias-chain depth versus residual-transition work and the accepted
  next design direction (not runtime implementation approval).
- `usage-failure/Main.fib`: minimized historical helper usage mistake, separate
  from the running experiments.
- `expansion-failure/`: abandoned full-parser construction checkpoint, separate
  from the running experiments. It is not type-validated or usable protocol code.

The three running fixtures read single octets, ASCII-lowercase printable bytes,
accumulate bytes, and stop reading when they see `:`. They output the accumulated
lowercase prefix only after draining the remaining induction steps. Colon is
included in the transition allowance but not output. They reject controls,
non-ASCII bytes, EOF before colon, or exhaustion without colon. They are **not
header token validators or frame parsers**: CRLF, lines, numeric length, body and
handlers are not implemented in these fixtures. Their boundary sizes are loop
input sizes, **not validated total-header-byte policies**.

### Existing linear continuation seam

The model is baseline pre-bulk `Frame.bodyStep` at git `27980d0`.
`primByteReadCase` returns a function accepting the linear induction continuation;
that function is applied to the induction continuation *after* branch selection.
The unrestricted read branches therefore do not capture that linear value.
Sharing the new byte accumulator also happens before binding that continuation.
A fatal branch consumes it syntactically in a bind continuation behind
`primRejectBytes`; this does not run after represented rejection. Completed
states drain via pure IO binds without additional reads. No arbitrary sharing
primitive, rollback, world token or exactly-once claim is introduced.

## Reproduction

Use a built Fibril executable explicitly. The measurements here used the
read-only baseline executable from the byte-IO worktree, with **this worktree's
explicit fixture source paths**:

```sh
FIBRIL=/Users/odunadeboye/dev/idris2/projects/fibril-byte-io/build/exec/fibril
python3 tools/probe_header_loops.py --fibril "$FIBRIL" \
  --sizes 14,31,32,33 --front-end
python3 tools/probe_header_loops.py --fibril "$FIBRIL" \
  --sizes 1023,1024,1025 --timeout 20
CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer' \
  python3 tools/probe_header_loops.py --fibril "$FIBRIL" \
    --fixtures flat32,nested32x32 --sizes 14,31,32,33
```

Every loop execution sends `a` repeated `N-1` times followed by `:`, and **keeps
stdin open** while requiring termination. JSON lines include the command,
phase, status, output length/hash, diagnostic, elapsed time and native metrics.
Native C is emitted from the actual checked fixture and compiled with `CC`.
The private metrics observer calls the unmodified binary runner and reports
steps/arena payload and the existing limits; it does not implement the loop.
Depth-limit attribution follows the existing runtime's evaluation-budget error
with steps below the step limit; no peak-depth instrumentation is added.

Artifacts use a private temporary directory and are removed. Output streams are
file-backed to avoid waiting for child exit with unread pipe output. A timeout
is recorded as `timeout`, never acceptance or a bounded-rejection success, and
makes the probe exit nonzero. Cleanup kills only the probe's own child process
group. An initial exploratory pipe-backed run timed out for hosted long inputs
at 20 seconds; the final file-backed rerun below completed them. Those initial
timeouts are **not** evidence of a semantic or evaluator-budget rejection.

## Observations at unchanged budgets

Initial syntax/payload limits remain 8192, expanded-core construction 200000,
hosted reduction fuel 4096, native pure depth 512 and native steps 100000.
Runner request/capacity and description budgets are untouched. All three loop
fixtures passed source checking, binary C emission and C compilation.

| Fixture | Input bytes | Hosted | Native steps / outcome |
| --- | --- | --- | --- |
| flat32 | 14 | exact output, success | 8165, exact output/success |
| flat32 | 31 | exact output, success | 15713, exact output/success |
| flat32 | 32 | exact output, success | 16157, exact output/success |
| flat32 | 33 | input rejection, no output | 15138, input rejection/no output |
| flat32 | 1023/1024/1025 | input rejection, no output | 15138 each, input rejection/no output |
| nested32x32 | 14 | reduction budget exhausted | 69376, pure-depth rejection |
| nested32x32 | 31 | reduction budget exhausted | 76210, pure-depth rejection |
| nested32x32 | 32 | reduction budget exhausted | 76612, pure-depth rejection |
| nested32x32 | 33 | reduction budget exhausted | 77014, pure-depth rejection |
| nested32x32 | 1023/1024 | exact output, success | 100000 each, step rejection |
| nested32x32 | 1025 | input rejection, no output | 100000, step rejection |
| flat1024 | 14/31/32/33 | binary checking recursion exhausted | 70589/77423/77825/78227, pure-depth rejection |
| flat1024 | 1023/1024/1025 | binary checking recursion exhausted | 100000 each, step rejection |

Thus nested small counts do not fix residual continuation evaluation at early
completion, nor the native step cost at maximum input. The successful hosted
long cases do not establish backend equivalence or header support. All budget
rejections above produced no stdout. ASan/UBSan runs of flat32/nested32x32 at
14/31/32/33 reproduced these outcomes with no sanitizer diagnostics.

### Earlier front-end errors (not the same failure)

The minimized usage fixture reports `Binder usage: expected 1, observed
unrestricted`: a linear indexed Nat was passed through unrestricted `ascii`.
Directly decoding the sliced bytes in the linear context fixes that helper.
Rechecking the earlier boxed-reader experiment with that fix accepted it;
there is **no evidence that boxing/continuation transport is inherently
untypable**. The initial broad attribution to the recursive continuation was
incorrect. The running fixtures contain the corrected helper.

The separate construction fixture reproduces `Expanded core construction
budget exhausted (200000)` at `withHeader`. It uses lexical parser helpers but
a wide function-valued Scanner record and transparent callback wrappers. It
also retains the historical helper error behind that construction gate; this
is a checkpoint of the first rejection, not an otherwise-correct implementation.
The relative contribution of state encoding versus transparent wrapper/global
substitution was **not isolated**. A subsequent multi-field state-record case
attempt also encountered the existing unary/binary pattern syntax boundary;
it was discarded, not worked around with core changes.

## Regression and follow-up boundary

The restored canonical production source passed all 14 existing framing tests
on hosted and emitted native paths (including maximum opaque binary bodies,
fragmentation/open stdin, two maximum frames and later-frame rejection).
The independent diagnostic sanitizer run above covers the new fixtures, not
the hosted compiler/FFI. No broad core regression build is claimed for this
evidence-only change; no shared package installation or caches were changed.

The smallest coordinated follow-up is to investigate **bounded read-dependent
iteration whose residual continuation can complete early without traversing a
large pure induction spine**, while preserving linear continuation use and
all current budgets. The flat1024 pre-execution checking-depth issue and
full-parser global expansion are additional distinct gates. These measurements
do not authorize a new primitive, compiler/runtime change or smaller product
cap. A fresh design approval is required before resuming production headers or
offering a callback to the parallel JSON lane.

## Accepted-iteration adoption checkpoint

On `feature/header-iteration-adoption`, based on `0bc9c85`, a fresh attempt used
[accepted bounded iteration](bounded-binary-iteration.md), native pairs and typed
abstract state. The supervisor approved **one bounded source simplification
investigation**, then explicitly stopped further parser growth after measuring
its results. This is not HEADER adoption. Production `Protocol/Frame.fib`, both
clients, JSON, compiler, runtime, transport, admission gates and all limits are
unchanged from `0bc9c85`. No `withFrame` API or private header-aware callback was
delivered. The existing canonical 0..4096-byte body contract remains production.

### Checked source milestone, not a frame parser

`tools/fixtures/header-iteration/names/Main.fib` is the preserved first compiling
milestone; `value-first/Main.fib` preserves the semantically equivalent hot-path
specialization. Both are outside production examples. The actual `.fib` code:

- Uses `primIterateBinary` with a compact 1024-byte-derived count, fixed state
  and result types, and an abstract four-field state. The count-entry ledger
  costs 2050 units, not a flat 1024-deep source Nat or a 4096-derived count.
- Counts **all** header octets, including CRLF/blank-line terminators, in one
  allowance across lines. Exhaustion rejects; it never resets the byte cap per
  line or drains unused induction continuations. At most 16 nonempty lines are
  admitted, plus the final empty CRLF line.
- Checks nonempty ASCII token names, strict CRLF and printable ASCII values.
  Names are accumulated casefolded; values and emitted header bytes are **not
  lowercased or normalized**. The lookup's folded result in value mode is used
  only for validity checking. Tabs, C0, DEL and non-ASCII are rejected. These are
  diagnostic lexer rules, **not a newly approved product whitespace policy**.
- Echoes only the complete raw header. It deliberately does **not** require or
  parse Content-Length, check duplicate fields, validate Content-Type/UTF-8
  policy, read a body, or invoke a body callback. Empty/duplicate/missing-length
  headers can therefore pass this diagnostic. It is not safe to use as a framer.

The native sharing box alone is lazy. An explicit `primBytesLengthIs Zero next`
guard demands the accumulated Bytes before forwarding it, preventing the prior
Bytes alias chain. It does not deeply demand the name String field. The loop's
state-WHNF rule is not arbitrary deep strictness.

### Admission and native cost attribution

These are **closed initial main** node/payload measurements, including the
fixture's closures, from the unchanged `tools/fixtures/json-admission/Measure.idr`
built against this worktree's private library. They exclude any nonexistent
body/handler/JSON integration; two separate libraries fitting 8192 would not
prove a combined entry fits.

Input is `X:` + `a` repeated `(N-6)` + `\r\n\r\n`, with stdin held open.
The classifier controls intentionally remove ASCII validation and name folding:
they are **NON-PRODUCTION**, generated cost controls, not candidate policies.
The aliases specialize reusable read/bind/case/Done/Continue helpers; value-first
also tests the common value phase before the other phase comparisons. The pure
response and string equality helpers were already lexical aliases.

| Source variant | Core nodes / payload | Native steps N=20 / 128 | N=1024: callbacks / reads, outcome |
| --- | ---: | ---: | --- |
| Preserved baseline | 2687 / 1212 | 14091 / 79971 | 159 / 159, step-budget rejection |
| Classifier removed, diagnostic only | 2582 / 1212 | 10353 / 50313 | 262 / 262, step-budget rejection |
| Aliases, original classifier | 2885 / 1212 | 13359 / 75027 | 170 / 170, step-budget rejection |
| Aliases + classifier removed, diagnostic only | 2780 / 1212 | 9621 / 45369 | 293 / 292, step-budget rejection |
| Preserved value-first + aliases | 2954 / 1226 | 12884 / 70448 | 182 / 182, step-budget rejection |

All five hosted runs accepted the 20/128/1024-byte value-padding inputs. **No
native 1024-byte header succeeded**: all reached exactly 100000 session steps,
wrote nothing and performed no final flush. No limit was raised. The extra
callback in the combined control reaches the budget before issuing its read.

Detailed native values for the preserved semantic hot variant:

| Input N | Steps | Peak pure depth | Arena payload / allocations | Callbacks / reads | Requests / reserved capacity | Consumed / accepted bytes | Flushes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 20 | 12884 | 48 | 480707 / 11569 | 20 / 20 | 21 / 40 | 20 / 20 | 1 |
| 128 | 70448 | 48 | 2807729 / 68269 | 128 / 128 | 129 / 256 | 128 / 128 | 1 |
| 1024 | 100000 | 48 | 4010542 / 97393 | 182 / 182 | 182 / 182 | 182 / 0 | 0 |

The successful diagnostic has one header write and only the mandatory final
flush. The arena numbers are retained arena payload/allocation counts, **not
live allocations after teardown, total heap or session/stdio storage bounds**.

The extra 108 `a` octets between the first two sizes cost 610 native steps each
in the baseline, 370 with classification removed, 571 with aliases, 331 with
both controls, and 533 with value-first. Thus the lookup costs 240 steps per
extra `a`; aliases save 39, and phase ordering saves a further 38 in this input
profile. This is local cost attribution, not extrapolated successful execution.
`primBytesIndex` materializes the octet as unary Nat; `primBytesSlice` traverses
it again. ASCII `a` costs 97+97=194 charged successor visits before lookup-wrapper
work. Even removing **all** classifier work leaves 331 steps per padded byte in
this representation. The minimal single-Bytes delimiter fixture's 89294 steps
at 1024 is not evidence that a multi-field parser also fits.

A further final-validation finding: the valid **82-byte** header whose single
name contains all ASCII token characters hits hosted reduction fuel4096. Native
baseline/hot paths reject at pure depth512 after 78 reads, using 54811/53296
steps, respectively. The lazy name accumulator is not covered by the Bytes
forcing guard; no deep-field fix was attempted after the approved stop. Short
independent headers cover every token character. This is another blocker, not
an implicit smaller name-length product policy.

### Focused validation and failed experiments

`tools/test_header_iteration.py` passed **10 source/observer tests** on hosted
and checked/emitted native paths. Coverage includes short mixed-case ASCII
names, unchanged values/raw output, all token characters in short independent
names, invalid/control/non-ASCII prefixes rejected with stdin open, strict CRLF,
truncations, and 15/16/17 nonempty lines. Hosted accepts total1023/1024 and rejects
1025, including two-line examples proving the cap does not reset at newline.
Corresponding native cases remain explicitly reported budget blockers, not
successes or golden requirements that future implementations must fail.

The named ASan/UBSan subset passed seven tests: all four observer/source-seam
unit tests, `test_short_ascii_names_values_and_strict_crlf`,
`test_invalid_ascii_tokens_controls_and_crlf_reject_with_stdin_open`, and
`test_nonempty_header_line_allowance_15_16_17`. This does not sanitize the hosted
compiler/FFI or claim sanitizer coverage of every long observation.

Four unchanged production framing regression methods passed on both backends:
`test_bulk_body_request_and_capacity_accounting`,
`test_unicode_count_is_encoded_byte_count`,
`test_two_frame_sequence_and_later_rejection`, and
`test_fragmented_open_input_completes_without_eof`. These cover zero/short/max
body accounting, opaque binary/Unicode, two4096-byte bodies, preserved earlier
output on later rejection, and live fragmentation/flush. They do not validate
an undelivered replacement header/body parser. Broad combined gates are deferred.

Earlier failures are retained honestly in the
[machine-readable observations](assets/evidence/header-iteration.json):

- Two initial source type errors (linear ASCII-helper argument and eta-short
  record eliminator) were fixed before measurements; neither was a QTT
  impossibility. One observer seam initially expected one callback site rather
  than the runtime's two sites and failed closed.
- A value-first control generator initially escaped CR/tab twice. Its20/128
  hosted/native runs produced **four30-second timeouts**, not passes or valid
  cost controls. The generator was fixed, its literal escapes tested, and the
  corrected source checked/emitted/rerun. Those failed rows are separate evidence.
- One Python edit typo initially prevented test import. The first complete
  focused invocation then failed an assumed-success long-name assertion; the
  final tests preserve that finding as an explicit budget observation. No source
  ASCII/case/control policy was relaxed to make validation pass.

Reproduce after a local build with the pinned real Idris2 and curated external
dependencies. Library installation/measurement, when requested, must use only
this worktree's `build/test-prefix`; no shared Pack install/cache is overwritten.

```sh
make -j8 header-iteration-test
python3 tools/probe_header_iteration.py --variants value-first \
  --measure /path/to/private/measure
CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer' \
  python3 tools/test_header_iteration.py HeaderIterationProbeTests \
  HeaderIterationSourceTests.test_short_ascii_names_values_and_strict_crlf \
  HeaderIterationSourceTests.test_invalid_ascii_tokens_controls_and_crlf_reject_with_stdin_open \
  HeaderIterationSourceTests.test_nonempty_header_line_allowance_15_16_17
```

The probe copies runtime sources privately and inserts counters only. Native
adapters observe real byte reads/writes/flushes; no C/Python header parser is
substituted. Processes have bounded foreground deadlines, and timeouts cause
failure. Exit zero from a probe means observations completed, **not** that budget
blockers passed. The source tests likewise identify long budget-blocked rows as
observations rather than successful header executions.

### Remaining decision, not an approved new primitive

A concrete general pure-data candidate is:

```text
primBytesLookupOctet : (1 table : Bytes) -> (1 key : Bytes) -> Bytes
```

Proposed semantics: if key is exactly one byte and its octet value indexes the
table, return that one table byte; otherwise return empty Bytes. This would let
source implement ASCII classification/case maps without constructing/traversing
a unary Nat. It is **not available or approved for implementation**, and would
require its own checking, accounting and lifetime review. It is a plausible
classifier improvement, **insufficient by itself**: even the weaker diagnostic
control costs331 steps per value octet. No proof excludes a different source
encoding, but this bounded investigation found no fitting semantic fast path.

Possible future strategies are a separately approved measured smaller explicit
pilot, batching with explicit buffering/overread semantics, or separately
reviewed transport/compiler improvements. A bounded read-through-delimiter
operation is only a possible batching direction, **not approved or delivered**.
No smaller product cap, new primitive/effect, rollback/callback semantics or
budget increase was chosen here. Content-Length uniqueness/decimal bounds,
Content-Type UTF-8 policy, unknown-header handling, validated-body `withFrame`,
full1024-byte native success and header+JSON combined admission all remain open.
