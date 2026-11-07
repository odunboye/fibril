# Typed-event lifecycle prototype (SOURCE ONLY)

This fixture is **not a wire LSP server, decoder, serializer or public library**.
`LSP.fib` implements a pure finite-state transition over typed events. No core,
runtime, primitive, admission, transport, parser or canonical Frame source is
changed. Cancellation, document storage, capabilities negotiation, diagnostic
bridging, EOF handling and workspace work are future integration, not implemented.

## Contract and representation

```text
transition : State -> Event -> Step
Step = { nextState : State, action : Action }
Event = Request RequestData | Notify Notification
RequestData = { id : RequestId, method : RequestMethod }
RequestId = NumericId Bytes | StringId Bytes
Action = Ignore | Respond ResponseData | Terminate ExitStatus
ResponseData = { id : RequestId, response : Response }
Response = InitializeAccepted | NullResult | Error ResponseError
```

**Validated-event PRECONDITION (not a refinement):** constructors are structurally
forgeable. A future decoder must validate ID kind/payload and classify request
versus notification and method:

- `NumericId`: ASCII bytes (therefore strict UTF8), JSON integer spelling;
  entire payload matches `-?(0|[1-9][0-9]*)`, signed32 range `[-2147483648,2147483647]`.
  Allow -0 and preserve opaque spelling; exclude leading +, leading zeros,
  fractions, exponents and bools. The range applies to the integer value without
  normalizing its stored spelling.
- `StringId`: decoded Unicode scalar-valid string represented as strict UTF8,
  NOT a raw quoted JSON lexeme. NUL is allowed in decoded payload via Bytes;
  no console-text claim follows. Quoting/escape decoding belongs to the future
  decoder, not this prototype.
- Null is not admitted as an LSP typed RequestId. Malformed/out-of-domain wire
  IDs and their error responses are future decoder obligations, not implemented
  or wire-tested here. This is not a claim about error responses for rejected
  wire IDs or general JSON-RPC null-ID policy.

Names do not validate wire data. No validation, normalization or ID comparison
occurs here. Requests return the supplied ID unchanged, including its kind.
There is no null-ID constructor and notifications have no ID field.

`Initialize`, `ShutdownRequest`, `OtherRequest` are request methods. `Initialized`,
`Exit`, `OtherNotification` are notifications. A request-shaped `initialized` or
`exit` belongs to `OtherRequest`; notification-shaped `initialize` or `shutdown`
belongs to `OtherNotification`. This is a **future classification obligation**, not
implemented routing. `OtherRequest` models an unsupported method, not execution of
any document method. Its response is MethodNotFound even for events sent while
awaiting `initialized`. `InitializeAccepted` is only a semantic success marker,
**not** a capabilities/serverInfo result. `NullResult` denotes shutdown's null
result, not serialized JSON.

Request/response fields are packed records inside unary constructors because the
existing source direct nominal cases support nullary/unary payloads. This source
representation is unrelated to JSON object shape. Erased kernel parameters,
explicit case motives and lexical function sharing prevent repeated expansion of
nested types; they add no operation or general promotion. The module is called
`LSP` inside this explicitly labelled fixture: shorter nominal keys also reduce
the existing payload estimate. No public production API is installed.

## Approved transition matrix

Cells are `next state / action`; `same` preserves the state.

| State | initialize request | shutdown request | other request | initialized notification | exit notification | other notification |
| --- | --- | --- | --- | --- | --- | --- |
| Preinitialize | AwaitInitialized / accepted | same / -32002 | same / -32002 | same / ignore | Terminated / failure | same / ignore |
| AwaitInitialized | same / -32600 | Shutdown / null | same / -32601 | Running / ignore | Terminated / failure | same / ignore |
| Running | same / -32600 | Shutdown / null | same / -32601 | same / ignore | Terminated / failure | same / ignore |
| Shutdown | same / -32600 | same / -32600 | same / -32600 | same / ignore | Terminated / success | same / ignore |
| Terminated | same / ignore | same / ignore | same / ignore | same / ignore | same / ignore | same / ignore |

Typed errors are ServerNotInitialized (-32002), InvalidRequest (-32600) and
MethodNotFound (-32601). Notifications never produce a response. Failure/success
are typed exit-status actions (nonzero/zero), **not process exits in this fixture**.
Terminated absorption is a pure-model convention to make the transition total;
a future real loop must stop reading after `Terminate`, not accept more messages.

Read-only reference: `../fibril-lsp/tools/fibril_lsp.py:dispatch` and
`../fibril-lsp/tools/test_lsp.py` lifecycle tests. The reference sets its initialized
flag while replying to initialize; its `initialized` notification is a no-op.
This prototype distinguishes AwaitInitialized only to observe that handshake:
it is **not an additional readiness gate**. Shutdown is valid before initialized;
other unsupported requests yield -32601 both before and after that notification.
The reference cancels actual jobs on shutdown; no such jobs/cancellation are
modeled here. Reference parameter validation and actual initialization payloads
are outside this typed boundary. Opaque numeric spelling preservation is a future
decode-boundary choice, not behavior proved for Python's parsed numeric values.
No total LSP compliance or parsed-wire integration is claimed.

## Actual checked differential evidence

`tools/test_lsp_lifecycle.py` generates fixed finite **typed source sequences**,
not JSON inputs. Its Python oracle is an explicit finite matrix; Python/C do not
implement a protocol decoder or the executing lifecycle transition. Both observers
invoke the **same** `transition`. The Idris harness checks the actual project and
runs the existing binary driver with recording adapters. C wraps genuinely emitted
source with the unchanged native runtime; it does not inject a raw lifecycle term
or rewrite runtime decisions/budgets. The only IO is in test consumers/adapters.

Each normal and ASan/UBSan run passed five test groups:

- Complete state/event matrix: 45 fixtures (15 request cells with **both** numeric
  and string ID `1`, plus 15 notification cells).
- Twelve bounded episodes (two to four events): normal handshake; unsupported
  request immediately after initialize and on both sides of initialized; shutdown
  without initialized; duplicate initialize while awaiting and running; repeated
  notifications; preinitialize errors; premature exit; post-shutdown requests;
  terminal absorption. Request-heavy episodes are split rather than exceeding
  admission; the matrix still observes every cell with full IDs.
- Eight opaque-ID fixtures: negative zero, signed 32-bit endpoints, empty string,
  quote/backslash/newline/CR/tab, embedded NUL, Unicode, 64-byte string. These are
  typed payload-preservation tests, **not wire-ID validation**. All eight payloads
  satisfy the precondition above, including -0 and decoded-string NUL. The matrix
  and episodes use numeric/string `1`, and the no-output consumer uses an empty
  decoded string; these also satisfy it. No existing fixture is an out-of-contract
  adversarial ID. Any future forged/out-of-domain fixture must be labelled
  **adversarial opaque preservation only, not a valid LSP ID**, rather than counted
  as decoder validation.
- Pure API entry/source-scope checks (`Transition.fib`).
- Actual no-output session (`NoOutput.fib`): demands the observation length before
  returning success. Both backends observed zero reads/writes, with only the
  session's mandatory final-success flush. Native reservations were zero requests
  and zero capacity. This is session evidence, not an inferred no-effect claim.

There are 65 exact-output fixtures per backend, plus one no-output session per
backend. Of those output fixtures, 53 are full-ID observations (45 matrix + eight
opaque-ID fixtures), and 12 are control-only episodes. All 133 evidence rows (130
outputs, two sessions, one pure admission row) are identical between normal and
sanitizer runs. No mismatch, unexpected rejection,
deadline or sanitizer finding occurred in those final runs. ASan/UBSan covers all
66 emitted programs and the normal-handshake real binary-stdio execution. All
commands have foreground deadlines; timeout/rejection is never a passing execution.

| Checked entry/client | Core nodes | Payload estimate |
| --- | ---: | ---: |
| Pure API (`Transition.fib`) | 4359 | 3209 |
| Largest full-ID single-event observation | 7344 | 5022 |
| Largest control-only multi-event observation | 8101 | 5729 |
| No-output consumer | 7033 | 4828 |

Payload is the existing conservative estimate (including repeated nominal names),
not merely wire/literal payload. Initial admission remains 8192 nodes /8192 payload;
construction 200000, checking depth512, hosted fuel/depth4096, native100000 steps,
pure depth512/16MiB arena/4096 pending all remain unchanged. Across the 65 native
output fixtures: 279–1215 steps, at most45640 arena payload bytes. No uniform bound
for arbitrary ID sizes or larger composition is established.

Output fixtures observed hosted reads/writes/flushes = `0/1/1`; native read calls
=0, final flushes=1, reserved requests=1 and capacity=exact output length. Native
byte-adapter writes equal output length (not write-request count). Thus these runs
show only the explicit test-driver output effect, not an implemented transport.

### Observation format and composition limitation

`Observation.fib` emits diagnostic bytes, **not JSON-RPC**: next-state tag
`P/A/R/S/T`, then `I` (ignore), `X0/X1` (terminate), or `Q` (response). Full response
observations add `N/S` ID-kind tag, one exact length octet, unchanged ID bytes, then
`A` (initialize marker), `N` (null), or `E-32002/E-32600/E-32601`. Test IDs are at
most64 bytes so the length octet is exact. This cap belongs to the diagnostic
observer, **not** a validated lifecycle ID policy.

`ControlObservation.fib` deliberately omits ID kind/length/payload after `Q` for
multi-event episodes. It shares state/response text encoding with the full observer;
ID preservation is tested independently with the full observer for every matrix
cell. Example normal control output: `AQARISQNTX0`.

The **full-ID four-event normal handshake does not fit**:8467 nodes/5796 payload;
source checking accepts it, binary C emission exits1 with `Native core admission
exceeds 8192 nodes`. This is a recorded composition blocker, **not an execution
pass** or a golden expectation that admission must always fail. Independent entry
fits do not establish full-observer session, server, header+JSON+LSP composition,
unbounded sessions, large payloads or scalability. No limits were relaxed to fit.
Earlier naive nested-type attempts exhausted construction or binary admission;
those exploratory failures are not counted as passes. No full repository/editor/
handbook suite was run for this fixture-only milestone.

## Reproduce

From the worktree, with the provided private environment/Pack adapter:

```sh
source /tmp/fibril-iteration-env.sh
export IDRIS2_PREFIX="$PWD/build/test-prefix"
I=/Users/odunadeboye/.local/state/pack/install/74b33730b6fea649b15e8d01ab099df9effcc7a0/idris2/bin/idris2
LSP_LIFECYCLE_EVIDENCE="$PWD/build/lsp-lifecycle-contract-normal.json" \
  make -j8 lsp-lifecycle-test PACK=/tmp/fibril-foundations-pack IDRIS2="$I"
LSP_LIFECYCLE_EVIDENCE="$PWD/build/lsp-lifecycle-contract-sanitized.json" \
  CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer' \
  make -j8 lsp-lifecycle-test PACK=/tmp/fibril-foundations-pack IDRIS2="$I"
python3 - <<'PY'
import hashlib
import json
from pathlib import Path
normal = json.loads(Path('build/lsp-lifecycle-contract-normal.json').read_text())
san = json.loads(Path('build/lsp-lifecycle-contract-sanitized.json').read_text())
assert normal == san
assert len(normal['rows']) == 133
recorded = json.loads(Path('tools/fixtures/lsp-lifecycle/evidence.json').read_text())
assert normal['rows'] == recorded['rows']
assert normal['inputs_sha256'] == recorded['inputs_sha256']
for path, digest in normal['inputs_sha256'].items():
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest() == digest
PY
```

All package installs are private `build/test-prefix`; temporary artifacts are
isolated and cleaned only by their owning test. [Recorded evidence](evidence.json)
contains typed event constructors (request payloads are hex), exact expected/actual
bytes, sizes, native costs and real session metrics. `inputs_sha256` records the
source, harness, test and contract-document bytes used by the run. The contract-only
review correction changes comments/documentation and textual regression checks,
not transition semantics or types. Both five-group suites are rerun for that
correction; the newly recorded 133 rows match the initial milestone rows exactly.
The composition-blocker observation is retained historical evidence from the
initial milestone, not a newly claimed execution. The event data reconstructs each
source with `source_for`; it is not a parsed wire trace. Independent review and
parent integration remain separate gates.
