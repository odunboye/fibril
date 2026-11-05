# IO roadmap

Status: proposal, not an implementation guarantee. Branch: `feature/qtt`.

## Existing implementation

The core has pure IO descriptions (`IOType`, `IOPure`, `IOBind`, `WriteLine`).
`Core/Erased.idr` checks their types, and `Core/Runtime.idr` checks runtime
resource usage. Bind requires a continuation whose result parameter is linear.
This constrains use of that parameter; it does **not** establish a linear world
token, make every IO description single-use, or guarantee exactly-once execution.

`Core/WeakHead.idr` contracts bind of pure and otherwise steps the action.
Full normalization in `Core/Reduction.idr` also traverses annotations,
continuations and pure operands inside descriptions. Neither reducer performs
host writes. No verified erasure, optimization or effect-preservation theorem
is claimed.

The hosted driver checks a closed `IO Unit` entry, prepares a complete bounded
list of `PrintLine` requests, and only then performs writes. The C backend also
plans before writing. Planning failure emits no output; host-write failure can
leave partial output. Both paths are bounded experimental implementations, not
sandboxes or transactional output systems.

The C backend accepts a smaller computational subset than the reference runner.
Consult `native-c.md` in the corresponding revision; supported data constructs
differ between worktrees. IO syntax support does not imply native support for
all pure computations used by an IO program.

## Consolidated implementation targets

These targets address limitations relevant to Fibril, not a claim that Idris 2
lacks linear IO internally: Idris 2 already threads a linear world token at its
low-level IO boundary. Reusable descriptions are not inherently a defect.

| Concern | Fibril today | Implementation target | Acceptance evidence |
| --- | --- | --- | --- |
| Effect granularity | One `IO A` type and stdout requests | Explicit capabilities for new privileged operations; choose their representation before adding file/network primitives | Helpers cannot acquire missing capabilities, including through closures or imports |
| Resource ownership | QTT usage checks and linear bind results; no general handle protocol | Creation, transfer, close and failure-path ownership rules | Reject duplicate/drop/double-close; accept transfer and balanced branch use |
| Failure coverage | Host `Either String` errors; no general source failure API | Distinguish domain errors, interpreter failures and process/foreign faults; design cleanup with recovery | Inject failures before/after requests and during cleanup; assert logs and retained ownership |
| Backend behavior | Hosted and native stdout planners with different computational limits | Shared observable contract and explicit support matrix | Differential output/error/order tests for the shared subset |
| Simulation and reasoning | Pure core descriptions; host output-only `prepareIO` | Scripted host interpreter and request trace; source-level abstraction is a separate design | Same program against scripted and real adapters, with deterministic input/error traces |
| Foreign trust | No general source FFI in this IO subset | Restricted ABI/marshalling and explicit ownership contracts | Reject unsupported signatures; test lifetime and encoding boundaries; document trusted foreign obligations |
| Concurrency | No structured concurrent IO in this subset | Deferred structured task scopes, cancellation and cleanup specification | Before shipping: no orphan tasks or lost capabilities on represented cancellation |

### Implementation boundaries

- `Core/Term`, `Core/Erased`, `Core/Runtime`, `Core/Usage`: type/resource
  representation and checking. Do not perform host effects here.
- `Core/Reduction` and `Core/WeakHead`: pure description computation only.
- `Source/Primitive`, elaboration and `stdlib/Prelude.fib`: checked source API.
  Core changes alone do not supply usable library operations.
- `Effect/Console`, `Driver/Console`, `Runtime/Console`, `Driver/Run`: request
  model, checked interpretation and host execution. Keep adapters injectable.
- `Driver/Native` and `runtime/native`: matching lowering, execution and errors.
- Core IO tests, `Tests.ConsoleSequence`, CLI and native suites: admission,
  ownership, request ordering, failure behavior and differential coverage.

## 1. Specify resource ownership before extending it

Decide whether ordinary reusable IO descriptions remain supported alongside a
separate resource-sensitive API, or whether a linear world/capability discipline
is required. Specify creation, transfer, duplication, discard, execution and
exceptional cleanup. Add positive and negative tests for each rule. Existing
linear bind-result checking is not sufficient evidence for this milestone.
See [the proposed ownership contract](io-ownership.md) and the
[host-only scoped file pilot](io-scoped-files.md). The latter tests cleanup and
revocation. Separate [abstract handle typing](io-static-handles.md) now checks
transfer and quantity/region rejection cases. An [inert core scope boundary](io-core-scope.md)
checks ownership-returning callbacks. A [host session registry](io-resource-session.md)
handles cleanup on represented interpreter failure. A [dedicated hosted resource
runner](io-resource-execution.md) now introduces checked scope handles and
validates their ownership return. Hosted [ownership-returning file reads](io-owned-file-reads.md)
now advance live generations; source handle creation is still disabled.

## 2. Design incremental execution and richer effects

An [inert core read request](io-core-input.md) now has an explicit EOF/line/error
result type and a checked incremental host interpreter. It is now exposed
to source programs through the [standalone interactive API](io-input.md).
The output planner and output-only emitter fail closed on it; explicit
interactive native emission and execution pass seven source-level hosted/native
differential cases. See [io-native-input.md](io-native-input.md).


Input cannot be implemented merely by adding a request to the complete output
plan: subsequent computation may depend on the response. Introduce a bounded
request/response interpreter and define the point at which effects occur.
Specify how failures after earlier writes differ from today's preflight model.
Keep execution outside conversion and type checking.

Candidate primitives are line input and arguments, followed by environment or
filesystem operations. Define EOF, encoding, platform behavior and represented
errors before choosing signatures; `ReadLine : IO String` alone does not express
EOF or failure. Validate behavior in both hosted and native execution.

## 3. Design typed failures and cleanup together

Evaluate explicit result types versus an error-indexed action type; changing
`IO` to `IO e a` is a proposal, not a settled requirement. Catching errors must
account for captured linear resources and cleanup when a continuation is skipped.
Host allocation failures, signals and foreign faults are not automatically
covered by a source-level error channel.

Tests should cover error propagation, recovery, cleanup, partial output and
uncaught errors. Avoid claiming arbitrary errors can be rendered without an
explicit rendering interface.

## 4. Scripted testing interpreter

A [typed host protocol and scripted interpreter](io-scripted.md) now exist in
`Effect/ConsoleProgram`, with twelve checks for input, EOF, failures and request
budgets. An incremental host interpreter supports injectable callbacks and real
writes; input is explicitly unsupported by the production adapter. These are
connected to checked core input through `Driver.Interactive`. A separate real host input adapter
handles LF/CRLF, EOF, errors and post-read length limits; see `io-scripted.md`.

Start with a host-side interpreter over checked core descriptions, with scripted
responses and an observable request log. `prepareIO` supplies an output-only
starting point, not an existing general source-language interpreter.

A Fibril-level `runPure` API would require a separate representation and typing
design: core constructors are not automatically source-inspectable free-monad
constructors. Compare scripted, hosted and native behavior on shared examples.

## 5. Restricted foreign boundary

Specify permitted signatures, marshalling, foreign trust assumptions and opaque
resource ownership. A linear `close` signature alone does not establish ownership:
creation, borrowing, transfer, exceptional paths and foreign retention all matter.
Do not claim arbitrary C signatures or memory safety are checked by Fibril.

## 6. Capability granularity

Before introducing privileged file/network operations, choose explicit capability
parameters or another checked permission representation. Do not require effect
rows merely to label existing stdout IO; capability passing may be sufficient.
Specify capability creation, authority delegation and whether a capability is
reusable authority or a linear resource. An effect label is not an OS sandbox.

## Delivery order and status

1. Establish runnable baseline tests and the hosted/native observable contract.
2. Implement and validate bounded planning improvements and output error handling.
3. Settle capability/ownership and failure/cleanup contracts before resource APIs.
4. Add a scripted request/response interpreter, then matching incremental hosted
   and native execution, then input primitives with explicit EOF/error behavior.
5. Introduce restricted foreign/resource operations only after ownership tests.

This document consolidates requirements; it does not implement those milestones.
The current branch has a proposed ownership document, hosted planner budget
changes and checked hosted stdout flushing. Run `python3 tools/test_io_hosted.py`
from the repository root for 246 core IO, console argument, sequence, script, input and resource checks,
plus real C `fflush` and checked-core stdin (Unicode CRLF/EOF/length failure)
smoke tests on Chez. These pass, including direct-core
64/65-write boundaries, injected write/flush failures, ordering and empty-plan
flushing. The runner uses temporary build output without pack or project/YAML
dependencies. Checked emission now lives in `Driver.Native.Emit`, with seven
source-to-C differential examples run by `tools/test_io_emitter.py` and
`make -j8 io-test`. The full CLI build, existing project/package tests and new
interactive CLI tests now pass under `make -j8 test io-test`. The earlier stall
was localized to the pre-existing project option parser; see
[build validation](io-build-validation.md). These passing regressions do not
constitute completed world-token IO or resource-safe exception handling.

Concurrency, cancellation and callbacks remain deferred until their lifetime and
cleanup semantics are specified. Hosted/native behavior already needs a shared
specification despite there being only one native backend. No unsafe execution
primitive is proposed.

## Validation

The current [console execution contract](io-execution-contract.md) records shared
observable behavior and backend limitations. `make io-test` runs the focused
hosted checks, 17 console-native runtime tests and 23
[resource-native runtime tests](io-native-resources.md) without the YAML dependency.
The direct runtime fixtures bypass source checking; a separate seven-example
source-to-C suite now exercises checked C emission and compares hosted output.
Seven further cases compare source-level interactive native and hosted file drivers.


Run the core IO, console planning, CLI and native suites for each target revision.
Record toolchain failures separately from test failures. Existing regressions are
finite evidence, not quantitative preservation or IO soundness proofs.
