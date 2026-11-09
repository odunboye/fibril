# Fibril

An experimental Idris-like language implemented in Idris 2, targeting a
quantitative De Morgan cubical core, C/JavaScript backends, and embedded profiles.

**Status:** a research prototype with a quantitative dependent core (erased typing
and runtime-usage checking), named modules with transparent globals and checked
imports, nominal data and records, explicit interfaces, and recursive functions
that are structural or admitted by a size-change check. Cubical term checking, a
JavaScript backend, embedded profiles and real-time guarantees are not implemented.
[Shared checked globals](docs/shared-checked-globals.md) retain named module bodies
once and use independently admitted references through checking, hosted execution
and native emission.
[Experimental C emission](docs/native-c.md) produces a real native executable for a checked subset (console and binary IO, pure data, bytes and `Word`); it is not yet an application backend: there is no native networking, storage, UI or FFI. See [guarantees](docs/guarantees.md) for what is and is not enforced.
[Native host embedding](docs/native-embedding.md) now lets a trusted C host run that subset with explicit output callbacks and structured failure results, without process-global console IO.

Fibril's HoTT direction remains a goal, not a present capability. The
[cubical alignment milestone](docs/cubical-alignment.md) sets out the first
checked path example and the quantitative obligations that must be resolved
before it enters the trusted core.

[Checked Fibril prelude functions](docs/console-runner.md) provide putStrLn,
pure, and bind over experimental IO descriptions. A hosted runner executes stdout
plans; a complete effect calculus and compiler backends remain future work.
[Unsigned 64-bit `Word` arithmetic](docs/words.md) (wrapping `+ - *`, comparison, `5w` literals) is checked,
evaluated by the reference runner and lowered by `emit-c`; `primWordToString` formats them as decimal text. [Pure byte operations](docs/bytes.md) now check and normalize separately from
text and have native lowering for the initial pure subset. [Checked binary
IO](docs/io-binary-source.md) is available through hosted `run-binary` and native
`emit-c-binary`, with separate admission from text/resource IO. [Explicit UTF-8 conversion](docs/utf8-values.md) is fallible
and preserves valid NUL without relaxing console output policy.
[Binary host embedding](docs/binary-embedding.md) now exposes checked binary programs through explicit host callbacks, with bounded IO and structured transport failures; checked frame validation is tested without process stdio.
An internal [binary transport pilot](docs/io-binary.md) preserves arbitrary bytes
through hosted/native stdio, with explicit budgets and checked flush. It is not
a self-hosted LSP runtime. A first [Fibril-written frame echo](docs/binary-framing.md)
now accepts canonical Content-Length frames with 0..4096-byte bodies, with one-
and two-frame clients. A 64-byte JSON diagnostic and typed-event lifecycle now
have checked hosted/native evidence, but are not a wire server. General headers,
scalable decoding and compiler-service integration remain blocked; see the
[current Fibril-written LSP status and next gate](docs/lsp-status.md).
See [checker scope and limits](docs/erased-checker.md). The [local module/import work](docs/modules.md) now has shared metadata parsing and read-only POSIX dependency discovery;
check/eval/run --source-dir now support checked closed qualified imports and
hosted execution. Version-2 project JSON retains source identity/snapshots; FibrilCheckProject validates project snapshots with conservative loaded-buffer
jumps. FibrilDefinitionProject provides checked cross-file lookup and opens targets automatically;
project-wide reference indexing and rename remain unimplemented.

The [Fibril LSP server](docs/lsp.md) supports unsaved buffers, UTF-16 positions,
diagnostics, checked project/package definitions, symbols, hover, formatting and
guarded same-file rename. Neovim uses a thin standard LSP client in `editors/nvim`;
other editors can launch the same stdio server. Module/file definitions and
references across checked application/package inventories are supported;
project-wide rename and completion remain unsupported. The [legacy Vim runtime](docs/editor-highlighting.md)
remains available during migration.

[Implicit arguments](docs/implicit-arguments.md) infer a declared erased prefix from direct global calls and supported expected results.

[Named function equations](docs/function-equations.md) allow `greet name = ...`
after an explicit signature; generated lambdas retain its quantities.

[Bare `Type`](docs/bare-type.md) is notation for `Type 0`; explicit higher
universe levels retain their existing meaning.

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
alternatives with explicit or inferred motives and linear branch joins, including qualified
direct imports. [General recursive data](docs/data.md#general-recursive-data) and
[indexed inductive families](docs/indexed-data.md) support whole-field positive
recursion, including length-indexed vectors with dependent case motives.
Nested/mutual recursive data and automatic index refinement remain future work.
[Compact alternatives](docs/data.md#compact-alternatives) write simple declarations as
`data T params = A fields | B fields`; indices and linear fields still use the `where` form.
Recursive function equations are accepted when structural, or when the
[size-change check](docs/function-equations.md#general-recursion) proves them terminating.

The first [application target is a transactional-email service](docs/applications/transactional-email.md).
Its source now lives in the standalone sibling `../email` project, not compiler examples;
only self-contained compiler regression snapshots remain under `test/fixtures/`. Network/TLS/storage integration, C deployment and the
web/mobile UI are not implemented; application blockers remain explicit. An optional
[trusted SQLite enqueue adapter](docs/durable-queue.md) now provides durable,
tenant-scoped idempotency. A [checked enqueue demonstration](docs/enqueue-worker.md)
now connects a bounded opaque-job validator to that store and acknowledges only
after commit; it is not yet an authenticated email application.

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
remains minimal. [Local packages can be locked](docs/lockfile.md) with `fibril lock` (change detection,
not pinning or authenticity). Workspace-member discovery, registries and version
solving remain future work.

Learn the language with the [Programming in Fibril tutorial](docs/tutorial/README.md).

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

Use the pinned Idris 2 collection through the project build from this directory:

```sh
make build
make unit-test
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

`make build` installs dependencies with Pack, then uses a worktree-local host
compiler adapter cached under `build/host-compiler/`. It defers construction of
termination-error call paths while retaining the original termination checks and
diagnostics. The installed compiler and collection pin are unchanged. The adapter
uses the collection's installed `idris2` API library and sources, and checks the
pinned revision and source hash before bootstrapping; see
[build performance](docs/build-performance.md) for measurements and details.
Use `make IDRIS2=idris2 build` or `pack build fibril` to use the stock compiler.
Run `make host-compiler-test` to compare checker outcomes, diagnostics and checked
interfaces against stock Idris.

Tests combine deterministic regressions with shrinking Hedgehog properties;
see the [testing guide](docs/testing.md).

Tests live in `test/src/Tests/`, with their own `test/tests.ipkg` depending
on `fibril`. Pack's test entry points to that package; tests are not included
in the compiler's source tree.

`make test` runs the private unit tests and CLI/native integration suites. Direct
`idris2 --build` remains possible, but may bypass collection selection unless it
is a Pack-managed shim. Review and test collection
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
