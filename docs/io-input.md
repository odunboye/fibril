# Standalone interactive input

Status: source primitives, checked Prelude wrappers, hosted interpretation,
native emission and standalone CLI commands implemented on `feature/qtt`.
The complete CLI builds and passes interactive command tests; see
[build validation](io-build-validation.md).

## Source API

```fib
readLine : IO ReadResult

readCase : (0 A : Type 0) -> (1 result : ReadResult) -> (eof : A) -> (line : (1 text : String) -> A) -> (error : (1 message : String) -> A) -> A
```

`ReadResult` has three internal alternatives: EOF, a line, or an error message.
Use `readCase` to consume it; no constructor names or dependent eliminator are
exposed in this first API. Line/error Strings must be consumed linearly. The
result type parameter is restricted to Type0, like the existing source IO API.

Branches are unrestricted because only one is selected. Therefore they cannot
capture linear ambient resources through this interface. This is deliberately
more restrictive than a future ownership-aware case construct; it does not
provide exception-safe resource cleanup or an intrinsically single-use action.

`readLine` and `readCase` are ordinary bundled Prelude definitions over
`primReadLine`, `primReadCase` and the erased `ReadResult` type global. The
eliminator is an ordinary checked core term over finite variants, not an axiom.

## Example

See [examples/core/read-line.fib](../examples/core/read-line.fib):

```fib
handleRead : (1 result : ReadResult) -> IO Unit
handleRead = \(1 result : ReadResult) => readCase (IO Unit) result (putStrLn "EOF") (\(1 text : String) => putStrLn (appendString "received:" text)) (\(1 message : String) => putStrLn (appendString "error:" message))

main : IO Unit
main = do
  putStrLn "prompt"
  (1 result : ReadResult) <- readLine
  handleRead result
```

After rebuilding the CLI:

```sh
./build/exec/fibril run-interactive examples/core/read-line.fib
./build/exec/fibril emit-c-interactive examples/core/read-line.fib > /tmp/read-line.c
cc -std=c11 -Iruntime/native /tmp/read-line.c runtime/native/fibril_runtime.c -o /tmp/read-line
printf 'hello\n' | /tmp/read-line
```

These commands accept standalone files, not package/source-dir options. Defaults
are 64 read/write requests and 8192 decoded characters per line. They check
`main : IO Unit` before exposing requests. Checking, evaluation and C emission
never perform input. Existing `run` and `emit-c` retain output-only preflight
semantics and reject computational input requests.

## Operational limits

Interactive execution can leave earlier output when a later computation, write
or budget fails. Stdout is flushed before reads; a prompt-flush failure becomes
a represented input error without attempting the read. Final flushing is checked
on success. Input can block; no timeout, sandbox or crash guarantee is provided.

Empty lines differ from EOF. LF/CRLF terminators are stripped; unterminated final
lines and bare final CR are preserved. Overlong lines are consumed and return an
error. Hosted length checks occur after allocation/decoding; native buffering is
bounded. Native rejects malformed UTF-8, while hosted decoding follows Idris/Chez;
only well-formed UTF-8 parity is currently tested.

`make io-test` includes seven source-level hosted/native comparisons using the
standalone file drivers, including EOF, Unicode and length failures. Full CLI
argument dispatch is covered by `make -j8 io-cli-test`; existing project/package
regressions also pass. Interactive package/source-dir options remain unsupported.
