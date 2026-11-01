# Hello world: restricted hosted console execution

Status: implemented first executable source slice. This is a **restricted console
entry profile**, not a general IO/effect calculus or C/JavaScript backend.

## Run it

~~~sh
pack build fibril
./build/exec/fibril run examples/core/hello-world.fib
~~~

[The source](../examples/core/hello-world.fib):

~~~fib
main : IO Unit
main = putStrLn "Hello, world!"
~~~

Output is exactly:

    Hello, world!

The runner uses the compiler's host runtime stdout adapter. It does not generate
a standalone Fibril executable, invoke a shell, require Node/Python, or execute
foreign code.

## The supported profile

The entire file must be one explicit main : IO Unit signature and matching
definition. Its body is either one putStrLn EXPRESSION call or a nonempty flat
do block of those calls. Every argument must be a closed ordinary expression
that checks as String and normalizes to a literal. Both headers start in column one on separate lines. The
signature is on one line; the body may continue on indented lines. Whitespace
and line comments are supported.

Arguments support ordinary applications, local let/lambda bindings, conditionals,
and parentheses. There are still no file-level helper declarations/aliases,
statement-level bindings, bind/result extraction, callbacks, imports, process
argument parsing, or other console primitives. IO, do, and putStrLn have
profile-specific meaning, not general core or monadic functionality.

check validates this complete grammar and reports:

    Console entry checking: accepted (restricted profile; pure String arguments core-checked)
    Type: IO Unit

The IO wrapper has a fixed validated signature, not a general effect-system
judgment. Its pure arguments now undergo ordinary core typing/resource checking,
normalization, and post-reduction checking before action data is produced. No action occurs
during check. check --erased rejects the profile, as does eval: reference
normalization never prints or admits IO as proof evidence.

## Compute a String argument

Run [the expression example](../examples/core/console-expressions.fib):

~~~fib
main : IO Unit
main = do
  putStrLn ((\(1 text : String) => text) "Hello from a pure function!")
  putStrLn (if False then "not selected" else "String computation works.")
  putStrLn (let (1 greeting : String) = "Local bindings work too." in greeting)
~~~

Each argument has its own empty outer context; local bindings inside it work,
but names do not leak between actions. This does not enable a helper declaration
before main, or an IO do-level let/bind. Erased extraction and linear discard
inside arguments are rejected before beta reduction can hide the violation.
Both branches must type-check, even when the condition is a literal.

[Driver.Console](../src/Fibril/Driver/Console.idr) is a pure planning service:
it resolves the argument, checks it against String, normalizes it, rechecks the
result, and requires an actual StringValue before constructing PrintLine. The
default normalization budget is 128 per argument; parser/checking depth is 256,
with independent type-reduction fuel 128. Exhaustion rejects the plan, never
executes a prefix, and is not a time/memory bound. The explicit prepareConsole
budget parameter is a host API, not a new CLI flag.

## Sequence console actions

Run [the sequence example](../examples/core/console-sequence.fib):

~~~sh
./build/exec/fibril run examples/core/console-sequence.fib
~~~

~~~fib
main : IO Unit
main = do
  putStrLn "Hello, world!"
  putStrLn "Fibril can sequence console output."
~~~

Actions execute in source order. All action lines must follow do, be indented,
and start at the same logical column. Each putStrLn and its expression must fit on
one physical source line. Blank lines/comments may separate actions. A do on its
own continuation line is supported, with actions further indented. Empty blocks,
nested do, semicolons, mismatched indentation, and trailing expressions fail.

The default parser cap is 64 actions per console entry; a single-print entry
counts as one. This cap and the file-byte limit are separate from execution-time
guarantees. The explicit parseConsoleWithBudget API permits testing the boundary.

The parser builds the **whole action list before execution**. A malformed 65th
action, unsupported later primitive, or bad later escape does not print the
earlier valid messages. Once execution begins, a represented output failure stops
the sequence; prior output is not rolled back. Buffered/OS failures retain the
limitations below.

This is sequencing of closed pure computations prepared into print requests,
not general monadic desugaring, effect inference, runtime variable binding, or
quantitative effect checking across shared action contexts.

## String data

Strings are double-quoted and preserve Unicode data subject to the existing
source-wide scalar/control policy. Supported escapes:

| Source escape | Decoded value |
| --- | --- |
| `\"` | Quote |
| `\\` | Backslash |
| `\n` | Line feed |
| `\r` | Carriage return |
| `\t` | Tab |

Raw tabs/line breaks, unterminated strings, and unsupported escapes fail with
located lexical diagnostics. There are no Unicode/numeric escape forms,
interpolation, multiline strings, or string operations. Ordinary pure String
values are now supported separately; see [String rules](strings.md).
A -- inside quotes is data, not a comment.

[Source.StringLiteral](../src/Fibril/Source/StringLiteral.idr) retains original
spelling separately from decoded data. The shared lexer emits a string token,
and Parser.literalValue shares decoding with ordinary String expression atoms.
Decoded data is not evaluated as code.

## Validation before execution

![Console validation is separate from ordinary normalization](diagrams/console-runner.svg)

1. The existing bounded loader reads, strictly decodes, and validates the file.
2. Shared lexing checks the **entire** source, including string escapes.
3. [Source.Console](../src/Fibril/Source/Console.idr) consumes all tokens, checks
   action count/layout, and retains ordinary named argument expressions.
4. [Driver.Console](../src/Fibril/Driver/Console.idr) prepares the entire checked,
   normalized String argument list into separate action data, without IO.
5. [Driver.Run](../src/Fibril/Driver/Run.idr) invokes the
   [runtime](../src/Fibril/Runtime/Console.idr) only after the full plan succeeds.
6. The adapter executes each PrintLine through host stdout, in order and stopping
   on the first represented failure.

Malformed/trailing source cannot execute a valid prefix. Program output goes to
stdout; run diagnostics go to stderr with nonzero exits. check/eval retain their
existing diagnostic stream behavior.

Output is not atomic: host writes may fail after partial output. Represented
fPutStrLn failures propagate, but host crashes, signals, buffering/flush failures,
blocking, and OS failures are not a complete structured-error guarantee.
This is not a sandbox or real-time profile.

## Trust and current boundaries

[Effect.Console](../src/Fibril/Effect/Console.idr) contains pure action data,
separate from Term. No IO constructor or effectful typing/reduction rule is added
to the ordinary core. Pure StringType/StringValue now exist there, independently
of this action profile. Console action/entry constructors are host data,
not unforgeable certificates. The file runner validates fresh source rather than
accepting caller-constructed action tags as checked programs.

The SourceProgram dispatcher distinguishes CoreSource from ConsoleSource.
ConsoleSource contains parsed, unchecked expressions until planning succeeds;
prepareSource alone does not authorize executing any action.
resolveSource cannot turn a console entry into Term 0, and runtime-source
preparation refuses console entries before normalization. The core modules do not
import the console parser, action type, or executor.

The 65,536-byte input limit remains; it is not a time/memory bound. There is no
general effect inference, resource accounting for effects, first-class IO, native/
web backend, general FFI, or compiled erasure. Those require an explicit design,
not extrapolation from one print primitive.

## Tests and next steps

[Tests.Console](../test/src/Tests/Console.idr) covers action validation, string
decoding/spans, full consumption, malformed input, and the erased/core boundary.
[Tests.ConsoleSequence](../test/src/Tests/ConsoleSequence.idr) checks do layout,
count limits, and order. A host callback fault-injection test exercises the actual
sequencer without touching stdout and verifies that later actions are skipped.
CLI tests assert exact output, Unicode/escapes, stderr failures with empty stdout,
and no printing from check/eval. [Tests.ConsoleArguments](../test/src/Tests/ConsoleArguments.idr)
adds pure applications/lets, argument type/resource failures, and explicit
normalization exhaustion. Tests include late parse/type/resolution failures and
exact/over-budget blocks. make examples checks/runs hello world and runs the sequence example.

Next: design the general effect/string representation, variable/bind semantics,
and real backends without moving effects into trusted normalization.
