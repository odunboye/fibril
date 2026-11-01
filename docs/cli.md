# Prototype CLI

Build with `pack build fibril`, then invoke `./build/exec/fibril`.

| Command | Behavior |
| --- | --- |
| --help (or no arguments) | Show available commands and implementation limits |
| --version | Show bootstrap version |
| check PATH | Parse/resolve one closed expression, check ordinary typing and runtime usage |
| check --erased PATH | Parse/resolve/check the erased ordinary fragment only |
| demo | Run built-in ordinary checking and cubical algebra examples |
| lex-source PATH | Print tokens and scalar spans for the minimal expression subset; not parsing/typing |
| validate-source PATH | Strictly decode a bounded UTF-8 file and validate source controls; not parsing/typing |

Unsupported commands and arguments exit nonzero. File-based expression checking
now exists; build/run commands for Fibril source do not. Pack builds the Idris
implementation. See the [expression grammar and checking guide](parser.md).

The [Unicode source guide](unicode-source.md) specifies byte/scalar offsets,
control policy, file-size limits, and concurrent-read limitations.

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
[Main](../src/Main.idr) handles arguments and IO only. Core modules do not import
the driver. These examples are not a parser, backend, or proof of soundness.

[Pretty](../src/Fibril/Core/Pretty.idr) supplies the diagnostic notation shared
with property-test counterexamples. Do not treat it as a specified surface grammar.

CLI smoke tests live in tools/test_cli.py and run through make test; pack test
fibril runs the Idris regressions/properties only. Python 3 is required for the
Makefile CLI checks. No additional Python packages are needed.
