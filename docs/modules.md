# First local module/import implementation contract

Status: shared **syntax/metadata parsing** and **read-only POSIX dependency
discovery** are implemented, alongside qualified syntax/explicit-global lookup.
**Checked imports are now available through check --source-dir ROOT ENTRY.**
Project check/eval/run share this checked preparation path when --source-dir is
explicit. Source-aware project JSON reports are implemented as version 2; a separate
FibrilCheckProject adapter consumes them with conservative loaded-buffer jumps. Plain
single-file commands do not silently choose a project root.

## Parsing progress

[Source.Document](../src/Fibril/Source/Document.idr) owns one parsed-document
representation for checking, symbols, and same-file navigation. It retains the
original tokens, EOF point, optional module header, imports, and expression or
declaration body. Module/import names retain component lists plus actual header
and name spans. Declaration metadata retains export markers and exact signature/
definition name selections.

Headers are column-one, each on one physical line. Module components have uppercase
ASCII initials and at most 16 components; keyword spellings such as String are
allowed as module-name components. At most 32 direct imports are parsed, duplicate
imports fail, and imports precede declarations. A named module has declarations,
not a bare expression. Empty module/library fragments need no main for metadata.

export occupies its own column-one line immediately before a signature/definition
pair (comments/blank lines may intervene). Definitions are private by default.
The marker requires a named module; it does not grant visibility or global
permissions before the loader checks the module. Its full symbol range includes
the modifier, but its selection remains the actual name token. symbols JSON now
adds an exported Boolean indicating the parsed marker, not checked accessibility.

Local declarations/parameters can be inspected with symbols/definition/references
in a module document whose body uses the existing expression grammar. Imported/qualified targets are not resolved by same-file navigation. Rename previews reject all module/import
documents until project-aware scope/interface checks exist. The new reserved words are module, import, and export; dots separate module
qualifiers, not value/member projections.

These services do not validate module/file identity, load dependencies, type-check
modules, enforce private access, or check imported calls by themselves; use the project checker for that. The existing headerless program path still uses ordinary core
checking and retains its regression suite.

## Qualified references and declared signatures

The expression parser now accepts full module-qualified names such as
Text.Greeting.greet. Prefix components follow the same uppercase ASCII rule as
module headers (including keyword components such as String); the final value is
an ordinary identifier, not a keyword or underscore wildcard. Names occupy one
physical line and have at most 16 module components plus the value name.

A qualified reference is a distinct AST form, not value projection or a string
looked up among local variables. A local value named Text cannot capture
Text.Greeting.greet. The explicit-global resolver can resolve such a reference
when its full name is supplied; it does not discover imports automatically.

Every global lookup, including prelude lookup, now enforces its declared type
with the checked identity ascription described below. A synthetic erased-mode
upward-universe regression demonstrates that inference returns the declared
signature rather than the narrower raw value type. Invalid supplied metadata
still fails core checking; global records are not axioms.

The project checker uses this import-binding boundary to install only checked
exports. Plain single-file check/JSON and eval/run still reject module/import documents
without the explicit project preparation path. Same-file navigation does not misidentify qualified names as local
variables and returns no cross-file target. Imported checking, name visibility, and elaboration admission now exist;
version-2 project JSON is available; FibrilCheckProject validates snapshots and maps only already-loaded source buffers.

The next language slice is specified in [Interfaces: explicit operations before
search](interfaces.md). Its runnable multi-file String/Bool operation example
uses current higher-order functions, not an implemented dictionary elaborator.

## Checked interfaces

~~~sh
./build/exec/fibril check --source-dir examples/modules/checked examples/modules/checked/Main.fib
~~~

[Main](../examples/modules/checked/Main.fib) calls an exported function from
[Text.Greeting](../examples/modules/checked/Text/Greeting.fib). Its private
decoration helper is checked but not exposed to importers. Checking the IO
description never prints its greeting.

[Driver.ModuleCheck](../src/Fibril/Driver/ModuleCheck.idr) consumes dependency-first
snapshots. It checks every named-module declaration, including private/unused
ones, before publishing that module's qualified export table. Environments contain
only direct imports plus the bundled prelude; transitive modules' names do not
leak. Earlier definitions in the current module are available unqualified and
through its own qualifier, including private definitions. No self-import is needed.

Named-module globals must be unrestricted and referenceable. Erased/linear
top-level globals remain rejected; function parameters can still be erased/linear.
The entry must define its own main; an imported main is not substituted. Libraries
need no main. Anonymous entries retain existing expression/typed-local-let behavior,
including the opaque local alias limitation.

The cumulative elaboration allowance is 200,000 core nodes. A conservative
syntax-size preflight uses cached global expansion weights before resolving/
cloning each declaration or anonymous entry. It includes annotations, global
identity ascriptions, repeated types, and named-entry materialization. Actual
resolved size is checked against the estimate as an internal consistency guard.
This is not a formal cost proof or a bound on normalization, type-operation
substitution, strings, process memory, or time. Conservative rejection is possible.

Errors preserve the affected snapshot's canonical file. Resolver points remain
real source points; core type/resource failures remain unlocated. Success is
human-readable stdout; represented failures use stderr and no acceptance prefix.
No project error is forced into the old single-file JSON/editor location model.

This first path checks closed transparent values, not opaque modules or abstract
types. It does not execute imported declarations, fetch packages, or add axioms.
Project eval/run now reuse this service; version-2 project JSON now preserves source identity and snapshots. FibrilCheckProject
consumes them separately from the version-1 single-file adapter.

Compiler-side definition lookup is now available through the explicit
[checked project definition API](editor-highlighting.md#checked-project-definition-api).
It returns a real target file/name span plus snapshots. FibrilDefinitionProject
consumes it with validated automatic target opening; the same-file gd is unchanged. Project-wide references/rename remain pending.

## Evaluating and running modules

~~~sh
./build/exec/fibril eval --source-dir examples/modules/checked examples/modules/checked/Main.fib
./build/exec/fibril run --source-dir examples/modules/checked examples/modules/checked/Main.fib
~~~

Both commands use the same graph/interface preparation as project checking.
Every dependency, including unused private definitions, is checked before entry
evaluation or planning. Sources used by the command are the loaded in-memory
snapshots; this does not make filesystem loading an atomic transaction.

eval normalizes the checked entry and rechecks the result against its original
type. It displays IO descriptions without executing writes. Project fuel is
configured with eval --source-dir ROOT --fuel N ENTRY (decimal 0..4096, default
128). Exhaustion or recheck failure reports no normal-form/acceptance prefix.

run requires IO Unit, prepares the full bounded output plan, then uses the host
stdout adapter. A dependency error, bad final type, or late plan failure executes
no output prefix. Actual host-write failures can still leave partial output and
are not rolled back. The [existing IO limits](console-runner.md) remain in effect;
successful project checking does not guarantee that planning fits its budgets.

Project success reports/program output use stdout; represented failures use
stderr. Core/planning/result failures without source provenance are file-level
entry errors, not guessed locations inside an inlined dependency. Original
dependency checking/resolution failures retain their dependency file.

This is hosted execution/reference evaluation, not C/JS generation. Unsaved project buffers, automatic loading from diagnostic lists,
project-wide reference/rename navigation, recursive modules, erased/
linear globals, and opaque interfaces are not provided by this path.

## Dependency discovery is now inspectable

~~~sh
./build/exec/fibril module-graph examples/modules/graph examples/modules/graph/Main.fib
~~~

ROOT and ENTRY are explicit filesystem paths interpreted from the process working
directory. The command returns version-1 JSON on stdout only after the entire
reachable graph loads. checked is always false: this is **not core checking**.
modules is dependency-first, with each canonical file once; entries include the
canonical path, declared name (or null for an anonymous entry), UTF-8 byte count,
and direct import names. Represented failures go to stderr with nonzero status
and no partial graph JSON.

[Driver.ModuleGraph](../src/Fibril/Driver/ModuleGraph.idr) retains each loaded
source String and shared parsed document. It checks canonical root containment,
exact-case directory components, requested/header names, named-entry mapping,
canonical-file aliases, cycles, and admission budgets. Libraries require a module
header but need no main. Headerless anonymous entries remain inspectable. Private
or exported declarations can be ill typed here: no interface is installed and no
Fibril expression or IO description is executed.

The diamond-shaped [graph fixture](../examples/modules/graph/Main.fib) demonstrates
reusing Shared through Left and Right. Its imports deliberately are not used for execution yet; qualified syntax parses and a separate project checker can validate imports.
check --source-dir invokes discovery before checking. The single-file check,
eval, and run paths do not.

Canonical paths use POSIX realpath through a small
[bootstrap host adapter](../src/Fibril/Runtime/Path.idr), not shell commands, cwd
mutation, or a Fibril foreign interface. This adapter targets the current POSIX
bootstrap; a Windows/non-POSIX implementation is not provided.

Current discovery limits are 32 distinct files/depth 32, 65,536 bytes per file,
and 524,288 aggregate UTF-8 bytes, counting reused snapshots once. A path-component
lookup examines at most 4,096 directory entries and stops on an exact match.
In oversized directories, whether a lookup exhausts that limit can depend on OS
enumeration order; do not treat that profile as deterministic admission for
arbitrarily large directories. Represented directory handles are closed on
success/failure.

Containment is checked at canonicalization time, not enforced with descriptor-
relative/no-follow opens. Concurrent filesystem/symlink replacement is **not**
sandboxed or transactionally detected. These are source-loading safeguards for
a trusted local filesystem snapshot, not an adversarial-filesystem security
boundary. Core expansion admission applies only in the project checker, since no inlining
occurs in this discovery command.

## Why this comes next

A real library needs file identities, checked dependencies, and explicit exports.
Those identities also underpin cross-file diagnostics/navigation and future
interfaces. We should establish them before expanding the monomorphic prelude.
Package fetching and a registry are separate work; see [packages](packages.md).

## File and module identity

The first graph has one explicit local source root. A logical module Text.Greeting
maps to Text/Greeting.fib beneath that root. Components use ASCII uppercase initials
followed by ASCII letters/digits/underscores. Names are case sensitive and are not
Unicode-normalized or silently case-folded by a case-insensitive filesystem.
The loader must check component spelling, not merely whether opening a path works.

Imported files must declare the requested name. A canonical filesystem identity
may not claim two logical module names. Resolve symlinks before checking containment
under the canonical source root; reject escapes and aliases with conflicting
identities. Module names are not arbitrary relative path strings: no parent
traversal, absolute paths, URL imports, or implicit directory search.

The three project command forms are implemented:

~~~sh
fibril check --source-dir src src/Main.fib
fibril eval --source-dir src src/Main.fib
fibril run --source-dir src src/Main.fib
~~~

The first implementation requires the explicit flag for project preparation.
A default root of the entry's directory is a possible later convenience, not
implemented implicit root search. Existing headerless entry files remain
supported as anonymous entry documents; importing
such a file is not supported. A named entry must also match its root-relative
file/module identity. Source roots are explicit inputs, not a YAML manifest
implementation or an automatic search up parent directories.

A module identity is the canonical local source root plus logical module name.
A checked snapshot additionally records source contents and compiler/foundation
configuration. This is not yet package identity or a persistent cache key.

## Imports, exports, and lookup

Proposed source (illustrative only):

~~~fib
module Text.Greeting

-- Private by default.
decorate : (1 name : String) -> String
decorate = \(1 name : String) => appendString "Hello, " name

export
greet : (1 name : String) -> IO Unit
greet = \(1 name : String) => putStrLn (decorate name)
~~~

~~~fib
module Main
import Text.Greeting

main : IO Unit
main = Text.Greeting.greet "Fibril"
~~~

Rules for the first parser/loader:

- At most one module header; imports precede declarations. Existing comments,
  scalar positions, explicit signatures, and column-one declaration framing stay.
- Definitions are private unless their signature has an export modifier. The
  modifier belongs to the whole signature/definition pair, not a separate value.
- Imports expose only explicitly exported names, through the full module qualifier.
  No open imports, aliases, wildcard exports, re-exports, or implicit transitive
  visibility in this slice. Duplicate direct imports are rejected.
- A file must directly import another module to use its qualifier. Its own
  qualifier is available for already checked, earlier definitions. Loading a transitive
  dependency does not install its names into every caller's source environment.
- Module qualifiers occupy a module namespace; a local value named Text cannot
  capture Text.Greeting.greet. Value member projection is not introduced by dots.
- Within a module, declarations remain nonrecursive and source ordered. Local
  unqualified bindings retain nearest-binder shadowing. No recursive modules,
  recursive declarations, or initializer execution.
- All installed module globals are closed, unrestricted definitions. Exporting
  or installing quantity-0/quantity-1 top-level globals is initially rejected;
  ownership and erased-global phase rules need their own representation first.
  Function parameters may still be erased/linear, including polymorphic functions.

Both exported and private definitions must be checked before any dependent
module uses the interface. An export is never an axiom. Imported IO values remain
inert descriptions; only the checked entry's run path can execute a plan.

## Declared types and conversion are separate obligations

Global resolution now embeds closed values through checked ascriptions. The prior
raw-value lookup could expose a narrower inferred type than a published signature.
The new lookup fixes that boundary, but is **not** a complete interface system:
the module loader still must check every definition before installing it.

For the first closed-global implementation, imported occurrences must enforce
the declared type using the existing checked-ascription elaboration:

    (Lambda Linear declaredType (Variable 0)) closedValue

Both terms are closed and validated before installation. This preserves the
signature at lookup while using existing core rules rather than a new typing axiom.
The entire resulting entry is still checked before acceptance/execution.

This representation is **computationally transparent**: conversion/reference
normalization can expose an inlined body through ordinary beta reduction.
Private means name visibility, not secret code or proof-level opacity. Public
bodies/types can contain checked closed private implementations. There is no
module-abstraction theorem or information-hiding guarantee.

Named-module top-level declarations use this closed-global path for same-module
references too, including private definitions. A module header therefore is not
merely ignored metadata. Headerless entry declarations and explicit local lets
keep the old lowering. Erased top-level aliases are rejected in the new path,
not quietly installed as unrestricted runtime values.

Earlier local declarations retain their existing [opaque-let limitation](declarations.md#important-opacity-limitation).
Imported closed values and local typed lets therefore have deliberately different
conversion behavior in this first slice. Document and test that difference.
Do not promise opaque imports, abstract types, transparent local aliases, or
change delta-unfolding policy silently. Proper opaque globals require a separate
core/interface design and rechecking affected artifacts.

## Dependency graph and atomic acceptance

![Planned checking boundary](diagrams/modules-first-slice.svg)

Load the full reachable graph using a visiting/checked state keyed by canonical
file identity. A visiting-node edge is a cycle and must report the actual import
chain. Check dependencies before importers; cache a checked module once per
invocation, but expose only each caller's direct imports. Do not conflate two
modules just because their exports have the same unqualified spelling.

The entry's main requirement remains an entry rule, not a library rule. A library
needs no main; an imported main is not selected as the entry. No module is accepted
partly because a budget ran out. Missing files, parse failures, private-name uses,
cycles, or checking failures abort the graph before any host output.

Initial proposed admission limits:

| Resource | Limit |
| --- | --- |
| Bytes per file | 65,536 UTF-8 bytes, existing loader |
| Distinct reachable modules, including entry | 32 |
| Aggregate source bytes | 524,288 |
| Declarations per module | 64, existing framing limit |
| Expanded core construction | 200,000 nodes, including annotations/ascriptions |
| Parser/check/type-reduction budgets | Existing independent limits |

The bundled bootstrap prelude is a compiler input, not a local graph node;
its existing source consistency/type checks remain required. Source snapshots are
immutable in-memory contents, not a claim of an atomic filesystem transaction.
A same-size concurrent edit is not detected by the existing bounded reader.

Charge expanded construction before cloning an imported body/type; source-size
and graph limits alone do not bound expansion from inlining. Count a reused file's
source bytes once. Repeated imports still charge each actual expanded occurrence.
These are rejection limits, not a proof of bounded time/memory: normalization,
substitution, string operations, and host allocation have separate costs.

No fetches, dependency install hooks, source plugins, implicit network access,
or package/workspace resolution are introduced. Foundations stay project-wide;
imports cannot choose a different kernel or admit unchecked proof assumptions.

## Provenance before cross-file editor integration

Retain the real source identity for module headers, import edges, declarations,
and export selections. Parsing/checking errors in a dependency must name that
file, not attach its line numbers to the entry. Core errors without provenance
remain unlocated even when the affected module is known.

The current version-1 JSON check adapter assumes scalar points belong to the
queried file. It must not receive a dependency point disguised as an entry point.
The explicit project JSON command now uses version 2 with file identities and
source snapshots. FibrilCheckProject consumes it with file/snapshot validation and conservative
already-loaded-buffer jumps. The older FibrilCheck consumer still rejects the
unsupported version rather than jump to a wrong source location.

Cross-file navigation should use module-qualified declaration identities plus
source snapshots. Existing position-based local targets are snapshot-local, not
stable project symbol IDs. Read-only dependency/cache policy and project-wide
rename are later work; today's same-file rename preview is not a project rename.

## Implementation order and acceptance tests

1. Parse module/import/export metadata with original token spans and a shared
   parsed-document representation. Do not create three independent header parsers
   for checking, symbols, and navigation.
2. Implement explicit-root identity, canonical containment/case checks, bounded
   graph loading, cycle diagnostics, and immutable source snapshots.
3. Check module declarations, preserve declared import signatures, enforce exports,
   and share the graph preparation service across check/eval/run.
4. Add source-aware check reports and consumers, then cross-file navigation.
5. Design explicit interface dictionaries and method quantities on this foundation;
   avoid treating the current concrete library functions as its final generic API.

Acceptance fixtures must cover two imported modules exporting the same leaf name;
private/transitive access rejection; header/path/case mismatches; root escape via
symlinks; repeated dependencies; cycles; bad dependency signatures; quantities;
polymorphic imported functions; signature preservation and transparent conversion;
library files without main; all graph/expansion limits; and no output prefix on
late dependency failures. Preserve every existing single-file example and test.

This contract is design work. Passing handbook/link tests validates its packaging,
not the unimplemented module semantics or metatheory.
