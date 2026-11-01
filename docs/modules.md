# First local module/import implementation contract

Status: design for the next implementation slice. **The loader, syntax, flags,
visibility rules, and graph budgets below are not implemented.** Existing check,
eval, run, navigation, and single-file declaration behavior remain unchanged.
This page records the boundary to implement and test, not a claim of module support.

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

Proposed CLI shape (not accepted today):

~~~sh
fibril check --source-dir src src/Main.fib
fibril eval --source-dir src src/Main.fib
fibril run --source-dir src src/Main.fib
~~~

Without the flag, use the entry file's directory as the source root. Existing
headerless entry files remain supported as anonymous entry documents; importing
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
- A file must directly import a module to use its qualifier. Loading a transitive
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

The current prelude resolver embeds closed values. A module loader must **not**
blindly treat that as a complete interface system. In particular, checking a value
against a declared type and then inferring the raw inlined value at a use site
can expose a narrower type than the published signature.

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
Introduce a source-aware protocol/version and update its consumers before
shipping module diagnostics through that path; older clients must reject the
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
