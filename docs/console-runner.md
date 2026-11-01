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
main = putStrLn STRING definition. Both headers start in column one on separate
lines. The signature is on one line; the body may continue on indented lines.
Whitespace and line comments are supported.

There are no helper declarations, aliases, arbitrary applications, parentheses
around the argument, do blocks, sequencing, callbacks, imports, argument parsing,
or other console primitives. IO and putStrLn are recognized names in this profile,
not general core constants or globally available functions.

check validates this complete grammar and reports:

    Console entry checking: accepted (restricted profile, not ordinary core checking)
    Type: IO Unit

This is structural validation of a fixed primitive signature and literal argument,
not ordinary core typing or a quantitative effect-system proof. No action occurs
during check. check --erased rejects the profile, as does eval: reference
normalization never prints or admits IO as proof evidence.

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
interpolation, multiline strings, string operations, or a core String type yet.
A -- inside quotes is data, not a comment.

[Source.StringLiteral](../src/Fibril/Source/StringLiteral.idr) retains original
spelling separately from decoded data. The shared lexer emits a string token,
but the ordinary expression parser explicitly rejects it. Decoded data is not
evaluated as code.

## Validation before execution

![Console validation is separate from ordinary normalization](diagrams/console-runner.svg)

1. The existing bounded loader reads, strictly decodes, and validates the file.
2. Shared lexing checks the **entire** source, including string escapes.
3. [Source.Console](../src/Fibril/Source/Console.idr) consumes all tokens and
   produces a separate ConsoleEntry/action.
4. [Driver.Run](../src/Fibril/Driver/Run.idr) invokes
   [Runtime.Console](../src/Fibril/Runtime/Console.idr) only after validation.
5. The adapter executes PrintLine through host stdout.

Malformed/trailing source cannot execute a valid prefix. Program output goes to
stdout; run diagnostics go to stderr with nonzero exits. check/eval retain their
existing diagnostic stream behavior.

Output is not atomic: host writes may fail after partial output. Represented
fPutStrLn failures propagate, but host crashes, signals, buffering/flush failures,
blocking, and OS failures are not a complete structured-error guarantee.
This is not a sandbox or real-time profile.

## Trust and current boundaries

[Effect.Console](../src/Fibril/Effect/Console.idr) contains pure action data,
separate from Term. No string/IO constructor, axiom, or new typing/reduction rule
was added to the ordinary core. Console action/entry constructors are host data,
not unforgeable certificates. The file runner validates fresh source rather than
accepting caller-constructed action tags as checked programs.

The SourceProgram dispatcher distinguishes CoreSource from ConsoleSource.
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
CLI tests assert exact output, Unicode/escapes, stderr failures with empty stdout,
and no printing from check/eval. make examples checks and runs hello world.

Next: design the general effect/string representation and sequencing rules, then
implement real backends without moving effects into trusted normalization.
