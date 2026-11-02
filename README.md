# Fibril

An experimental Idris-like language implemented in Idris 2, targeting a
quantitative De Morgan cubical core, C/JavaScript backends, and embedded profiles.

**Status:** an annotated expression frontend and small nonrecursive declaration
files, with erased typing and an ordinary runtime-usage prototype. Full modules,
transparent global definitions, cubical term checking,
compiler backends, and real-time guarantees are not implemented.
[Checked Fibril prelude functions](docs/console-runner.md) provide putStrLn,
pure, and bind over experimental IO descriptions. A hosted runner executes stdout
plans; a complete effect calculus and compiler backends remain future work.
See [checker scope and limits](docs/erased-checker.md). The [local module/import work](docs/modules.md) now has shared metadata parsing and read-only POSIX dependency discovery;
check/eval/run --source-dir now support checked closed qualified imports and
hosted execution. Version-2 project JSON retains source identity/snapshots; FibrilCheckProject validates project snapshots with conservative loaded-buffer
jumps. FibrilDefinitionProject provides checked cross-file lookup and opens targets automatically;
project-wide reference indexing and rename remain unimplemented.

Optional [Neovim/Vim highlighting, checking, and same-file navigation](docs/editor-highlighting.md),
including [LazyVim installation](docs/editor-highlighting.md#install-in-lazyvim),
is available for .fib files. Navigation uses a saved-buffer CLI command; cross-file
navigation and an LSP server remain future work.

Record parsing and generation now use a [separate elaboration layer](docs/elaboration.md).
Use fibril elaborate PATH to inspect expanded named IR (explicitly unchecked).

A [conservative formatter](docs/formatting.md) is available as fibril format PATH
or fibril format --check PATH. It normalizes token spacing and safely lays out long applications, lambdas, signatures and cases,
without writing files or changing comments/literal spelling.

The abstraction contract is documented in [the interface contract](docs/interfaces.md),
with a runnable multi-file generic String/Bool operation example. Erased named
globals now support exported type abbreviations without granting runtime access;
dependent pair formation/construction/elimination are now in the core.
A resource-budgeted named-record prototype now runs, without a fixed field-count cap; see [record foundations](docs/records.md) and [singleton rules](docs/unary-records.md). [Explicit interfaces and named implementations](docs/explicit-interfaces.md) now
lower to checked dictionary values and method functions. Implicit dictionary
search and algebraic-law checking remain unimplemented.
[Typed record patterns](docs/pattern-inference.md) now infer constant motives
for independent results; dependent results retain explicit return clauses.

## Build

Use the Idris 2 `pack` tool from this project directory:

```sh
pack build fibril
pack test fibril
./build/exec/fibril --help
./build/exec/fibril demo
./build/exec/fibril run examples/core/hello-world.fib
./build/exec/fibril run examples/core/console-sequence.fib
./build/exec/fibril run examples/core/console-expressions.fib
./build/exec/fibril run examples/core/io-functions.fib
./build/exec/fibril check examples/core/identity.fib
./build/exec/fibril eval examples/core/evaluate-identity.fib
./build/exec/fibril eval examples/core/unit.fib
./build/exec/fibril eval examples/core/string-identity.fib
./build/exec/fibril eval examples/core/declarations.fib
```

`pack.toml` pins collection `nightly-260903`, which selects Idris 2
0.8.0 at commit `74b33730b6fea649b15e8d01ab099df9effcc7a0`.
Initial validation used pack commit `846a90d76d1d4c451484eb09773f11a9e2fd58f2`.
Pack itself is not installed or pinned by the project configuration.
A C toolchain and the collection's Scheme implementation are bootstrap
requirements; these are not Fibril backend choices.

Tests combine deterministic regressions with shrinking Hedgehog properties;
see the [testing guide](docs/testing.md).

Tests live in `test/src/Tests/`, with their own `test/tests.ipkg` depending
on `fibril`. Pack's test entry points to that package; tests are not included
in the compiler's source tree.

`make build` and `make test` wrap the pack commands. Direct `idris2 --build`
remains possible, but bypasses collection selection. Review and test collection
upgrades explicitly; do not use a floating collection for project builds.

See [examples](examples/README.md) for runnable bootstrap programs and clearly
labeled proposed Fibril scenarios, including proofs.

Run `make bench-smoke` for validated benchmark smoke checks or `make bench`
for exploratory timings. Results and environment metadata are written to
`build/benchmarks/latest.json`; see [measurement limits](docs/benchmarks.md).

Learn the implementation through the [Building Fibril textbook](docs/book/00-orientation.md):
eight ordered chapters with exercises, diagrams, and linked source.

Build the browsable handbook with `make handbook`, or use `make serve-docs`
to browse at http://127.0.0.1:8000. It includes diagrams, a curated call graph,
linked source pages, API reference, and the full design record.
See [handbook prerequisites](docs/handbook.md).

Generate API documentation with `make docs` (`build/docs/index.html`);
use the matching Idris 2 compiler as explained in the
[documentation policy](docs/documentation-policy.md).

See [documentation](docs/README.md) and [first milestone](docs/milestone-01.md).
