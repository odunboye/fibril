# Header parser investigation: stopped, no production extension

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
