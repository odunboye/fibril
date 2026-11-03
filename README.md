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

The [inductive-data milestone](docs/inductive-data.md) now has an implemented
[internal finite-variant kernel](docs/finite-variants.md), with dependent cases,
nullary/payload arms and quantity checks. [Closed nominal identity](docs/nominal-data.md)
now preserves declaration keys and phantom arguments in the internal kernel.
[Checked declaration construction](docs/data-declarations.md) now allocates keys
and generates independently checked closed families/constructors with exact admission.
[Non-recursive source data](docs/data.md) now declares nominal constructors and
optional consuming eliminators, including dependent multi-field payloads and imports.
[Direct data cases](docs/direct-data-cases.md) now match nullary/unary
alternatives with explicit motives and linear branch joins. Wider/qualified
patterns, recursive inductives and structural recursion remain future work.

The first [application target is a transactional-email service](docs/applications/transactional-email.md),
with a checked relay-submission model. Network/TLS/storage, C deployment and the
web/mobile UI are not implemented; application blockers remain explicit.

Create a runnable console project with `fibril new mailer` (or preview using
`--dry-run`); see [project creation](docs/project-creation.md). This offline scaffold
generates fibril.yaml with the documented default namespace `App`. Use
`--module-prefix Mailer` to override it or `--source-only` for a minimal source tree.
Namespaces are never inferred from directory names. Inside a generated project,
use `fibril check`, `fibril run` or `fibril module-graph`: these select only
./fibril.yaml, without searching parent directories.

The [local workspace contract](docs/workspaces.md) now has a tested pure planner
for package order and direct-dependency namespace ownership. [Strict manifest
inspection](docs/manifests.md) now works as `fibril manifest PATH`, using a pinned
maintained YAML parser. [Explicit local packages](docs/local-packages.md) now
check/run through one ownership-aware multi-root graph using `--package fibril.yaml`.
[Standalone libraries and pure Bool test suites](docs/libraries-and-tests.md) now
work through `fibril new NAME --lib`, `fibril check` and `fibril test`, without a
dummy application entry. App scaffolds include a separate test package with a starter Bool suite
too; replace its True result with real application assertions. `--source-only`
remains minimal. Workspace-member discovery and locks remain future work.

Start with the [feature use-case guide](docs/use-cases.md) for what each feature
is for, when to use it, and when a simpler alternative is better.

The abstraction contract is documented in [the interface contract](docs/interfaces.md),
with a runnable multi-file generic String/Bool operation example. Erased named
globals now support exported type abbreviations without granting runtime access;
dependent pair formation/construction/elimination are now in the core.
A resource-budgeted named-record prototype now runs, without a fixed field-count cap; see [record foundations](docs/records.md) and [singleton rules](docs/unary-records.md). [Explicit interfaces and named implementations](docs/explicit-interfaces.md) now
lower to checked dictionary values and method functions. [Named method blocks](docs/implementation-blocks.md)
can now construct those dictionaries from local or checked direct-import interface schemas.
Recursive/implicit global instance search and algebraic-law checking remain unimplemented.
[Named constraints and local dictionary selection](docs/constraints.md) now
support explicit @{dictionary} and unique-local @{} applications.
[Opt-in @{implementation} lookup](docs/visible-implementations.md) selects a unique
checked visible named implementation without recursive search.
[Named infix calls](docs/infix.md) now support backtick function/method applications
with fixed left associativity, ordinary quantities and no parser-special library operations.
[Explicit implementation factories](docs/implementation-factories.md) now reuse
wrapper operations across types through header-scoped named method blocks;
factory application remains explicit, without recursive lookup.
[Typed record patterns](docs/pattern-inference.md) infer constant or canonical
dependent motives within resource bounds; explicit return clauses retain control.
Named record/interface eliminators are optional; omitted helpers are not generated.
[Constructor-named structural patterns](docs/constructor-patterns.md) validate
transparent packing and can infer field types and quantities from the constructor
signature. [Erased constructor parameters](docs/pattern-parameters.md) can also
be inferred from structural scrutinee-type constraints; explicit arguments remain
available when inference cannot recover them.

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
