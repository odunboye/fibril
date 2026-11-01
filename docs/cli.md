# Prototype CLI

Build with `pack build fibril`, then invoke `./build/exec/fibril`.

| Command | Behavior |
| --- | --- |
| --help (or no arguments) | Show available commands and implementation limits |
| --version | Show bootstrap version |
| run PATH | Validate and execute the restricted main : IO Unit console profile through the host adapter |
| eval PATH | Check then reference-normalize an expression or declaration program (default fuel 128) |
| eval --fuel N PATH | Same with evaluation fuel 0..4096; not compiled execution |
| check PATH | Parse/resolve an expression or declaration file with main, then check typing/runtime usage |
| check --erased PATH | Parse/resolve/check the erased ordinary fragment only |
| demo | Run built-in ordinary checking and cubical algebra examples |
| lex-source PATH | Print tokens and scalar spans for the minimal expression subset; not parsing/typing |
| validate-source PATH | Strictly decode a bounded UTF-8 file and validate source controls; not parsing/typing |

Unsupported commands and arguments exit nonzero. File-based expression checking
now exists, and run executes the restricted console profile. A Fibril source
build/backend command does not exist. Pack builds the Idris implementation. See the [expression grammar and checking guide](parser.md).

The [Unicode source guide](unicode-source.md) specifies byte/scalar offsets,
control policy, file-size limits, and concurrent-read limitations.

See [checked reference evaluation](evaluation.md) for evaluation modes, budgets,
post-reduction checks, and why this is not a backend runtime.

Files may contain a single expression or [source-ordered declarations](declarations.md)
with explicit signatures and a main entry. These lower to typed lets, not
transparent globals; all limitations and column-one framing rules are explicit.

For [hello world](console-runner.md), use run: check validates the console profile
without printing, while eval and check --erased reject effects. run reserves
stdout for program output and sends failures to stderr. It is hosted execution,
not generated C/JS or general IO typing. Flat do blocks can sequence up to 64
print requests with closed pure String expressions. Every argument is checked,
reduced, and rechecked before any action executes.

## Source diagnostics

Located frontend failures now include filename, line/column, a bounded source
excerpt, and a caret. Tabs are shown as one space; coordinates count scalars, not
terminal cells or UTF-16. Core failures have a filename but no fabricated source
caret. Type mismatches include inferred/expected core types; branch mismatches
include both inferred branch types, and shape errors show the type found.
See [diagnostics](diagnostics.md) for escaping, bounds, payloads, and API details.

## Follow the demo

```sh
./build/exec/fibril demo
```

The report prints a polymorphic identity in explicit core notation:

    Identity term: (Lam 0 Type0 (Lam 1 v0 v0))
    Identity type: (Pi 0 Type0 (Pi 1 v0 v1))

It checks the expected type in erased mode, checks runtime resource usage, rejects
a separate linear-duplication example, and exercises interval equality and face
boundaries. Closed usage [] means no free variables are consumed.

[Driver.Demo](../src/Fibril/Driver/Demo.idr) orchestrates these calls. It returns
an error instead of printing unchecked success if an expectation fails.
[Main](../src/Main.idr) handles argument dispatch; the separate console runtime
adapter performs the new hosted printing. Core modules do not import
the driver. These examples are not a parser, backend, or proof of soundness.

[Pretty](../src/Fibril/Core/Pretty.idr) supplies the diagnostic notation shared
with property-test counterexamples. Do not treat it as a specified surface grammar.

CLI smoke tests live in tools/test_cli.py and run through make test; pack test
fibril runs the Idris regressions/properties only. Python 3 is required for the
Makefile CLI checks. No additional Python packages are needed.
