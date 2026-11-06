# Core input request: first kernel slice

Status: typed inert core syntax with checked hosted/native execution and a
[source-level input API](io-input.md).

`Core.Term.ReadLine : Term n` describes input and has type
`IOType readResultType`. The internal result shape is:

- tag 0: EOF, no payload;
- tag 1: line, a quantity-1 String payload;
- tag 2: represented input failure, a quantity-1 String payload.

This reuses the existing finite-variant checker and eliminator. Both String
payloads must be consumed according to ordinary resource rules. The result is
structural, not a new nominal source datatype or an IO exception channel.

Full and head normalization leave the request inert. Renaming, substitution,
structural proofs, usage checking, scope transport and elaboration accounting
include the new constructor. It consumes no free variables; this does not make
an unrestricted description intrinsically single-use or implement world-token IO.

The complete-output planner and output-only native emitter reject input
requests. An explicitly selected interactive native emitter supports them. The source `readLine` wrapper exposes the request only to explicit interactive
execution; existing output execution is unchanged.

`Driver.Interactive.prepareInteractive` checks a closed `IO Unit` entry before
exposing a host protocol program. It head-exposes descriptions with bounded pure
reduction, turns host input responses into checked variant values and feeds
those values into bind continuations. It rechecks intermediate results and the
final Unit. Represented input errors reach the error alternative; write errors
stop interpretation. No host effects occur in this driver or during conversion.

Description depth, reduction fuel and host request fuel are separate budgets.
Unlike preflighted output, a later interactive computation/check can fail after
earlier requests. The caller owns request interpretation and final flushing.
Scripted tests cover all alternatives and write/request failures; real stdin
smoke tests exercise checked core programs, prompt flushing, Unicode CRLF, EOF
and input length failure.

Source exposure uses the checked `readCase` eliminator described in
[io-input.md](io-input.md). A [separate native interactive runtime](io-native-input.md)
is directly tested, and `emitCheckedInteractiveC` now lowers checked input
programs. Seven source-level differential cases compare it with hosted execution. The
output-only emitter continues to reject input. This does
not establish a world-token or exception-safe linear-resource discipline.
