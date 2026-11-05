# Scripted host console protocol

Status: implemented host-side protocol, now used by the checked interactive
[source input API](io-input.md). The protocol datatype itself is host-only.

`Fibril.Effect.ConsoleProgram` separates typed requests from their responses:

- `WriteRequest text` returns `Either String ()`.
- `ReadLineRequest` returns `Either String (Maybe String)`.
  `Right (Just line)` is input, `Right Nothing` is EOF and `Left message` is a
  represented input failure. The host adapter's newline and decoding behavior
  is described below; source programs use the separate `readLine` API.

A `ConsoleProgram a` is either `Finished a` or `Await request continuation`.
Continuations can construct subsequent requests from the response. These are
host Idris values, not new Fibril terms or inspectable source IO constructors.
No changes to conversion or core typing are implied.

`runScript fuel script program` is pure. Each request consumes one unit of fuel;
a finished program requires none. A script provides expected write text and
write responses, or input responses. Request-kind/text mismatches and missing
responses are interpreter errors. Represented operation errors are instead
passed to the continuation, which chooses whether to recover or stop.

The result retains a matched transcript, unused script and either the returned
value or interpreter error. An unmatched request is not consumed. If a later
request fails, the already matched transcript remains visible. Nothing in this
interpreter performs host effects.

`Driver.Console.prepareConsoleProgram` checks and fully plans a closed source
`IO Unit` term before adapting it with `outputProgram`. The latter adapts a
prepared `List ConsoleAction`, stopping on the first represented write error. It does not flush: flushing belongs to the
host execution boundary, and scripted write success does not imply successful
host output or flushing.

## Validation and remaining integration

Scripted checks run in the normal Idris test entry and `make io-test`.
The focused runner supports `IDRIS2` for selecting an installed compiler without
changing package-manager state.

`Runtime.Console.runConsoleProgram` interprets the same protocol incrementally
with injectable write/read callbacks and request fuel. Operation errors are
responses that continuations may handle; fuel exhaustion is an interpreter
error. Earlier callbacks may already have performed effects. It performs no
implicit flush. `runOutputConsoleProgram` uses the real write adapter but
responds to input with an explicit unsupported error. Neither function is the
source `run` entry point; source `run` retains complete stdout preflight and
checked final flushing.

Host checks compare response-dependent scripted and injected execution,
check fuel after a visible prefix, write failures and unsupported input.

`Runtime.Console.recordConsoleProgram` is an opt-in incremental interpreter
that returns the observed requests and responses alongside its outcome. Its
transcript can be supplied directly to `runScript` for pure replay, including
represented operation failures and the prefix preceding request-budget
exhaustion. Recording tests also exercise real file EOF. The ordinary interpreter
remains unrecorded to avoid retaining potentially sensitive input/output.
Transcripts describe protocol responses, not hidden host effects, process
exceptions or a final flush. Replay assumes the same host program and request
budget; it is not a source-language determinism proof or a persistent trace
format.
`Runtime.ConsoleInput.readConsoleLine` borrows a host file and returns a decoded
line without its final LF or CRLF. Empty lines are `Just ""`; EOF is `Nothing`.
An unterminated final line (including a bare trailing CR) is preserved. The
adapter checks the host file error flag explicitly and does not conflate read
failure with EOF. Byte collection is capped at four times the supplied character
limit plus CR/LF; decoded scalar length is checked afterwards. Overlong lines
are drained without retaining further bytes. Strict UTF-8 decoding and explicit
NUL rejection avoid C-string truncation. Valid U+FFFD is preserved. This is not
binary IO, a total-allocation bound or a nonblocking implementation. The borrowed
handle is never closed by the adapter; C-compatible execution is tested on Chez.

`runInteractiveConsoleProgram` connects real stdin to the protocol with request
fuel and a per-line limit. Before each read it flushes stdout; a flush failure
is delivered as the read response without attempting input. There is no implicit
final flush. Existing source `run` is unchanged. Focused tests exercise real stdin
with Unicode CRLF input and EOF, plus injected prompt-flush ordering and errors.

`Driver.Interactive.prepareInteractive` now bridges checked closed core
`IO Unit` terms to incremental requests, including the inert core read request.
See [io-core-input.md](io-core-input.md) for the distinct failure semantics and
real stdin checks. Explicit native input lowering now has ten checked-core
source-level differential cases; see [io-native-input.md](io-native-input.md).
The [standalone source API](io-input.md) and full CLI validation are implemented;
interactive package integration and stronger resource ownership remain separate work.
