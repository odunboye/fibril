# Prototype CLI

Build with `pack build fibril`, then invoke `./build/exec/fibril`.

| Command | Behavior |
| --- | --- |
| --help (or no arguments) | Show available commands and implementation limits |
| --version | Show bootstrap version |
| new NAME [--lib] [--template console] [--module-prefix PREFIX or --source-only] [--dry-run] | Fresh offline console scaffold; POSIX trusted cwd, no overwrite; see [project creation](project-creation.md) |
| new --help | Scaffolding usage and input policy |
| check --package PATH | Check an explicit [local package closure](local-packages.md), with direct package and module permissions |
| run --package PATH | Check the full local package source graph before preparing/executing host stdout |
| module-graph --package PATH | Syntax-only graph JSON including package inventory and source owners; no typing/execution |
| manifest PATH | [Strict local YAML schema inspection](manifests.md) as JSON; checked/resolved/locked false, no dependency traversal or source checking |
| test [--package PATH] | Check inventories/imports before bounded pure Bool suite evaluation; True passes, False fails, exhaustion errors; no source IO |
| check / run / module-graph | Use ./fibril.yaml only; no parent search or malformed-manifest fallback. --package PATH remains an explicit override. |
| run PATH | Runtime-check main : IO Unit, prepare all output requests, then execute through the host adapter |
| eval PATH | Check then reference-normalize an expression or declaration program (default fuel 128) |
| eval --fuel N PATH | Same with evaluation fuel 0..4096; not compiled execution |
| check PATH | Parse/resolve an expression or declaration file with main, then check typing/runtime usage |
| module-graph ROOT ENTRY | Read-only POSIX dependency discovery as JSON; no core checking or execution |
| run --source-dir ROOT ENTRY | Check the full project, prepare IO Unit output plan, then execute host stdout |
| eval --source-dir ROOT ENTRY | Check modules, normalize entry, and recheck without performing effects |
| eval --source-dir ROOT --fuel N ENTRY | Project reference evaluation with fuel 0..4096 |
| check --source-dir ROOT ENTRY | Check bounded POSIX dependency graph and closed qualified module interfaces; no execution |
| check --json --source-dir ROOT ENTRY | Version-2 project report with source paths/snapshots; JSON on represented rejection |
| check --json PATH | Structured runtime-check report; JSON on stdout even on represented rejection, with nonzero status |
| check --erased PATH | Parse/resolve/check the erased ordinary fragment only |
| rename-preview LINE COLUMN NEWNAME PATH | Conservative capture-checked same-file edit preview as JSON; never writes files |
| format PATH | Conservative spacing and guarded structured-expression layout to stdout; no source writes |
| format --json PATH | Version-1 original/formatted text snapshot report for editor use |
| format --check PATH | Empty success for canonical spacing; nonzero when formatting is required |
| elaborate PATH | Inspect expanded named declaration IR; checked:false, no import loading or effects |
| reference LINE COLUMN PATH | Tagged built-in documentation or bundled Prelude declaration snapshot; syntax/lexical lookup |
| references LINE COLUMN PATH | Same-file lexical occurrences, including declaration sites, as JSON |
| definition --source-dir ROOT --entry ENTRY LINE COLUMN PATH | Checked project definition; version-2 file/range target and source snapshots |
| definition --package MANIFEST LINE COLUMN PATH | Checked application or library-inventory definition; version-2 packet across its loaded package graph |
| definition LINE COLUMN PATH | Same-file lexical target as JSON, using one-based scalar coordinates; errors on stderr |
| symbols PATH | JSON declaration ranges, syntax only; errors on stderr |
| demo | Run built-in ordinary checking and cubical algebra examples |
| lex-source PATH | Print tokens and scalar spans for the minimal expression subset; not parsing/typing |
| validate-source PATH | Strictly decode a bounded UTF-8 file and validate source controls; not parsing/typing |

Unsupported commands and arguments exit nonzero. File-based expression checking
now exists, and run executes prepared stdout requests from checked IO descriptions. A Fibril source
build/backend command does not exist. Pack builds the Idris implementation. See the [expression grammar and checking guide](parser.md).

The [Unicode source guide](unicode-source.md) specifies byte/scalar offsets,
control policy, file-size limits, and concurrent-read limitations.

See [checked reference evaluation](evaluation.md) for evaluation modes, budgets,
post-reduction checks, and why this is not a backend runtime.

Files may contain a single expression or [source-ordered declarations](declarations.md)
with explicit signatures and a main entry. These lower to typed lets, not
transparent globals; all limitations and column-one framing rules are explicit.

For [hello world](console-runner.md), putStrLn is a checked Fibril prelude function.
check checks IO descriptions without printing; eval displays their pure normal
forms; check --erased grants no runtime permission. Only run executes a complete
checked IO Unit output plan. It reserves stdout for program output and sends
failures to stderr. Hosted execution is not generated C/JS or a completed effect
calculus. Ordinary helpers and flat do sequencing are supported.

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
