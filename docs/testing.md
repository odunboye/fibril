# Testing Fibril

## Layers

1. Deterministic regressions: explicit positive/negative examples, including
   erasure policy, scope checks, beta budgets, and erased checker failures.
2. Hedgehog properties: randomized structural laws with integrated shrinking.
3. Runnable bootstrap examples and generated handbook/API checks.
4. Host-checked finite permission and structural binding proofs; broader
   term-metatheory proofs and differential/typed-generation coverage remain future.

Run `make test` or `pack test fibril`. Both deterministic checks and properties
must pass; a failure exits nonzero. Run `make examples` and `make handbook`
when completing a documented task.

Runtime-specific deterministic checks in
[Tests.Runtime](../test/src/Tests/Runtime.idr) cover exact use, erased arguments,
closure capture/duplication, and diagnostics. Erased generators are not treated
as evidence for runtime safety.

[Tests.SourceText](../test/src/Tests/SourceText.idr) covers Unicode preservation,
selected forbidden controls, CRLF/tab handling, and scalar error locations.
Those tests operate on decoded strings, not identifiers. Tests.UTF8 separately
covers malformed bytes and encoding boundaries. CLI tests exercise raw files,
byte limits, missing paths, and a fixed-seed malformed corpus cross-checked with
Python's strict decoder; neither suite establishes full decoder correctness.

[Tests.Frontend](../test/src/Tests/Frontend.idr) now checks expression parsing,
name resolution, associativity, shadowing/domain scope, budgets, source extents,
ascriptions, and erased/runtime integration. `make examples` checks ASCII/Unicode identity
sources and an erased type expression. These are ordinary expressions, not full
module/elaboration or cubical-source coverage.

Optional `make python-embed-test` compiles/runs standalone C embedding tests
against the selected CPython development installation. It is not part of make
test or pack test and does not establish Fibril FFI support. See
[Python interoperability](python-interop.md).

[Tests.Evaluate](../test/src/Tests/Evaluate.idr) and CLI tests exercise checked
source normalization, exact/exhausted fuel, and rejection before reduction.
The output is reference normal form syntax, not C/JS execution.

[Tests.Let](../test/src/Tests/Let.idr) checks local binding scopes, annotations,
quantities, nonrecursion, and reference reduction. CLI examples use explicit in;
there is no declaration/layout generalization yet.

[Tests.Unit](../test/src/Tests/Unit.idr) covers the first data primitive. Scope and
erased typed generators include both atoms; an additional runtime property checks
closed Unit programs and their normal forms. The incompatible-expectation property
uses the recipe's expected type to avoid falsely rejecting the new Unit : Type0 seed.

[Tests.UnitCase](../test/src/Tests/UnitCase.idr) tests explicit Unit elimination,
including scrutinee validation, resource accounting, exact fuel and weak/full
reduction differences. Structural, erased typed, and runtime generators include
UnitCase wrappers in their existing typing/structural properties.

[Tests.Boolean](../test/src/Tests/Boolean.idr) checks both constructors, branch
selection/types/resources, constant-condition negative cases, nested syntax,
computational type conversion, and comparison exhaustion. Existing scoped, erased,
and runtime recipes now include conditionals; a permission-preservation recipe
adds coverage of differing branch observations.

[Tests.Alternatives](../test/src/Tests/Alternatives.idr) exhausts the finite
permission algebra and validates ambient permissions. The former branch-equality
counterexample must now evaluate and recheck. A generated two-variable context
exercises branch discrepancies under unrestricted permissions before/after
one step and full normalization; this samples admissibility, not exact usage equality.

[Tests.Diagnostic](../test/src/Tests/Diagnostic.idr) and file CLI tests validate
bounded escaped excerpts, scalar carets, line endings/EOF, preserved structured
errors, and absence of guessed source spans for core failures.

[Tests.CheckDiagnostic](../test/src/Tests/CheckDiagnostic.idr) checks mismatch
payloads in closed/open scopes, branch and shape errors, rendering without
normalization, typed driver propagation, and distinct evaluation exhaustion.
Existing rejection tests now check constructor payloads as well as outcomes.

[Renaming laws](renaming.md) prove identity, composition, pointwise congruence,
and weakening commutation structurally in Idris 2. Tests.Renaming checks concrete
witness instantiations across every constructor and noninjective maps. Existing
sampled structural tests remain; those theorem witnesses add no randomized properties.

[Substitution laws](substitution.md) now prove congruence, identity, and variable-only
renaming correspondence. Tests.Substitution instantiates the signatures and a
concrete binder/domain capture witness.
[Composition/fusion laws](substitution-composition.md) now also have total host
proofs. Tests.SubstitutionComposition checks their instantiated signatures and
the shared replaceNewest map. The existing sampled composition/instantiation
properties remain regressions alongside the host theorems.

[Tests.Beta](../test/src/Tests/Beta.idr) checks instantiated host proofs for
instantiation naturality and known-root beta compatibility. Counterexamples
ensure nobody generalizes this to false arbitrary step/substitution commutation.
These are theorem-witness regressions, not additional randomized properties.

[Tests.Fuel](../test/src/Tests/Fuel.idr) instantiates splitting, successful-budget
stability, exact resumption, and no-next-step theorems. A new randomized fuel
splitting property uses raw scoped terms and budgets 0..2 per chunk; it compares
result tags and exact syntax. Deterministic cases also retain an ill-typed loop
and demonstrate why arbitrary Normal tags are not certificates.

[Tests.Declaration](../test/src/Tests/Declaration.idr) and CLI tests validate
signature/definition framing, source order, nonrecursion, entry presence, budgets,
quantities, dependent signatures, and the explicit opaque-let limitation.

[Tests.Console](../test/src/Tests/Console.idr) covers string literals and the
ordinary IO functions without executing effects. CLI tests assert exact
hello-world/Unicode output, complete planning before execution, stdout/stderr
separation, and inert eval/erased checking.

Optional `make editor-test` runs [real headless Neovim/Vim checks](editor-highlighting.md)
for lexical group positions, filetype detection, quoted data, Unicode, reloads,
and option undo. It needs no compiler, plugin manager, or network, and is not a
prerequisite of the default suite. The handbook includes the Vimscript sources.

Handbook highlighting regressions cover Idris/Fibril token spans, stable source
line anchors and exact text (including blank lines), HTML/fence safety, and
light/dark token contrast. These use the existing local Pandoc prerequisite.

[Tests.ConsoleSequence](../test/src/Tests/ConsoleSequence.idr) checks console do
blocks, exact/over-budget action counts, layout, and separation from proofs and
normalization. IORef-backed fault injection verifies the production sequencer's
order and first-error stopping behavior without stdout. CLI tests ensure late
source errors execute no prefix. Randomized-property counts are unchanged.

[Tests.String](../test/src/Tests/String.idr) covers primitive String typing,
literal equality/rendering, Unicode/escapes, quantities, and pure computation.
Structural/erased generators include both String constructors; binding theorem
witnesses now include them. A new closed-String runtime recipe checks expected
literal normal forms without checker filtering. Console isolation tests remain.

[Tests.ConsoleArguments](../test/src/Tests/ConsoleArguments.idr) checks the pure
console planning boundary: closed String applications/lets/conditionals,
normalization exhaustion, and rejection before reduction can hide type/resource
violations. CLI late-argument failures must leave stdout empty; name errors keep
real source carets while core errors stay unlocated at the subterm level.

[Tests.IO](../test/src/Tests/IO.idr) checks primitive signatures, Fibril prelude
installation, name shadowing, universe levels, linear/erased failures, and inert
normalization. CLI tests run ordinary helpers and shadowed putStrLn outside the
repository. A generated IO-description property compares plans before/after
normalization without executing writes. make build checks the generated prelude.
IO map regressions additionally cover ordinary-library identity/composition examples,
output order, captured linear values, invalid result usage/function quantities, and
explicit rather than implicit flattening of nested IO descriptions.

Typed do-binding regressions check annotation/RHS scope, sequential visibility,
shadowing, mandatory linear quantities, missing continuations, wrong action/result
types, explicit Unit consumption, and rejection of discarded/duplicated results.
CLI tests check exact output and no prefix on late binding failures, including
original source carets for unresolved names.

Do-let regressions cover mixing pure/IO bindings, unrestricted reuse, shadowing,
nonrecursive RHS/annotation scope, wrong value types, quantity violations, erased
unused descriptions, final-let rejection, and compatibility with complete let-in
actions. CLI failures after an earlier write must still execute no output prefix.

Explicit do-result regressions cover single-action ascriptions, general result
threading through bare actions/let/result bindings, invalid result types, wrong
continuation results, and linear use. Polymorphic and type-name-shadowing examples
exercise weakening rather than re-resolving the block's annotation. CLI tests
check output order, inert eval, non-Unit main rejection, and no late-error prefix.

Document-symbol tests check signature/definition name selections, quantities,
source order, library fragments without main, empty/expression documents, atomic
failure, and independence from resolution/typing. CLI tests parse the versioned
JSON, verify original-source slices with Unicode/CRLF, and ensure errors produce
no partial JSON on stdout.

Navigation tests use marked cursor/target fixtures for top-level order, parameter
and Pi scopes, nearest shadowing, nonrecursive let/do RHSs, and block-result type
annotations. Unicode/CRLF/tab cases check scalar positions; comments, strings,
parentheses, wildcards, unknown/prelude names, and forward/self references miss.
The pure API accepts unsaved Strings. CLI tests also cover invalid coordinates,
malformed files, and missing paths, keeping error stdout empty.

Optional real-editor navigation tests run the saved-buffer command in both
Neovim and Vim when a local compiler is built. They check UTF-8/combining scalar
conversion, CRLF/Unix snapshots, quoted filenames, refusal of modified/stale
buffers, malformed responses, missing executable, cursor preservation on misses,
and buffer-local command/mapping cleanup without overriding gd.

Same-file reference fixtures mark every expected occurrence and query point.
They check source-ordered signature/definition/binder inclusion, shadowed groups,
nonrecursive RHSs, do bindings/result annotations, Unicode/CRLF source slices,
and exclusion of comments, literals, unresolved/forward names, and wildcards.
The pure API is also tested; malformed-file and coordinate errors return no JSON.

Real-editor reference-list tests cover both Unix and CRLF files, UTF-8/combining
byte conversions, location-window creation, source cursor preservation, and both
command/Plug cleanup paths. Misses, stale/modified buffers, malformed JSON, and a
partly valid result array must not replace prior location lists.

Rename-preview tests cover local/top-level/do binders, nonrecursive RHS scope,
polymorphic result annotations, growth/shrinkage and no-op edits, Unicode/CRLF
preservation, and exact original-source ranges. Negative cases cover capture of
resolved/unresolved/prelude names, duplicate declarations, entry-point changes,
invalid/oversized names, and UTF-8 byte-limit crossings. CLI tests apply previews
only to temporary test strings and assert the command itself never writes source.
These are deterministic regressions, not a formal alpha-renaming theorem.

Editor rename-preview tests exercise real Neovim/Vim with Unix/CRLF sources and
Unicode/combining prefixes. They verify the read-only scratch diff, simultaneous
same-line replacements, unchanged string literals/source buffers/cursors, command
and Plug cleanup, and refusal of no-op/keyword/modified/malformed requests.

String append extends raw and constructed typed generators, binding witnesses,
and the closed-String result recipe without adding checker-driven filtering.
Deterministic tests check both-operand typing, exact Unicode concatenation,
linear-use addition, pre-reduction quantity errors, head forcing, and fuel limits.
CLI tests verify computed greetings and empty stdout after late argument errors.
Existing host structural and fuel proofs compile over the extended datatype;
this is not a quantitative preservation or string memory-safety theorem.

String equality extends raw/typed generators, binding witnesses, and the
closed-String recipe through generated comparison-driven conditionals. Tests
cover exact/unequal/empty/decomposed Unicode text, operand typing and linear-use
addition, erased/duplicated-input rejection, head forcing, fuel, and Bool-only
results. CLI tests check both greeting branches and no late-error output prefix.
Host syntax/fuel proofs compile; this is not a dependent equality theorem.

Boolean-library tests exhaust the finite notBool/andBool/orBool truth tables,
check ordinary lookup/shadowing/partial application and exact-once parameters,
and reject duplication, erased extraction, and wrong operand types. CLI tests
exercise combined String/Boolean output and verify that a constant-result path
cannot hide a late type error. No new primitive or metatheory claim is introduced.

Structured check-report tests cover acceptance, type/resource rejection, source
points versus unlocated core errors, and inert IO descriptions. JSON tests cover
quotes, backslashes, controls, and Unicode. CLI tests parse accepted/rejected
reports, check scalar positions with Unicode/CRLF, keep decoding byte offsets
separate, and cover source-policy and missing-file failures without program output.

FibrilCheck real-editor tests cover located resolver errors with UTF-8/combining
prefixes, unlocated typing/resource failures, nonjumpable EOF/BOM/byte-offset
entries, accepted IO descriptions without execution, and command/Plug cleanup.
Malformed JSON, inconsistent statuses, partly invalid diagnostics, coordinate
mismatches, and modified buffers must preserve prior lists and source files.

Shared document tests cover module/import/export spans, private defaults,
keyword-name components, header placement, duplicate imports, missing signatures,
component/import budgets, and unchanged headerless checking. CLI tests verify
symbols/visibility-marker JSON and local navigation with Unicode/CRLF, explicit
module execution refusal, and conservative module rename rejection. Metadata
parsing is not evidence of filesystem loading or semantic export enforcement.

Module-graph CLI tests cover dependency-first diamond reuse, syntax-only
acceptance, canonical/header identity, aliases, exact-case lookup, missing imports,
cycles, root/symlink escape rejection, anonymous entries, count/aggregate byte
limits, and no execution or partial JSON. UTF-8/quoted root paths and actual byte
counts exercise the POSIX canonical-path adapter. This is not imported type
checking or an adversarial-filesystem/sandbox proof.

Qualified-name tests cover keyword module components, component budgets,
one-line spelling, rejection of member projection/wildcards, and separation from
local prefix names. Explicit supplied-global tests check linear application,
upward declared-signature preservation, transparent conversion, and rejection of
invalid metadata. CLI graph inspection parses qualified bodies without claiming
checking; ordinary checking still rejects modules or reports unbound qualifiers.

Checked-module CLI tests cover private/public interfaces, polymorphic imports,
qualified leaf-name separation, own-module qualifiers, transitive-name exclusion,
checking unused private definitions, global quantity rejection, own-main selection,
and legacy anonymous-entry opacity. A doubling import chain exhausts the core
expansion allowance before unchecked expansion; failure stdout stays empty.
IO descriptions are checked without executing output. These are prototype
regressions, not a module abstraction/typing preservation theorem.

Project runtime tests execute the two-module private-helper greeting, normalize
IO descriptions without writes, evaluate polymorphic imports, and reject non-IO
run entries. Zero/invalid fuel, late entry errors, invalid unused dependency
bodies, and oversized action plans must leave stdout empty. Dependency failures
retain their actual file; post-evaluation/planning errors remain unlocated.

Project JSON tests distinguish entry/dependency identities, original Unicode/CRLF
snapshots, located resolver errors, unlocated runtime failures, byte-only decoding
errors, unavailable policy-error text, missing imports, and known empty sources.
Existing real-editor tests confirm version-1 clients reject version-2 reports
without changing their lists. No cross-file editor consumption is claimed yet.

## Hedgehog dependency

Repository: https://github.com/stefan-hoeck/idris2-hedgehog

The test package alone depends on hedgehog. The pinned pack collection currently
selects version 0.6.0, revision
`f413d4bb7010063dedb15f29839accbc0617c4d4`. Compiler/library packages do not depend
on Hedgehog. Collection upgrades must review this dependency as well.

The upstream README/tutorial were inspected before integration. The tutorial
recommends applicative generator composition for better shrinking where possible.
The library supports coverage checks and reproducible recheck calls; the inspected
README lists no state-machine testing or parallel execution.

## Current properties

[Tests.Properties](../test/src/Tests/Properties.idr) runs eleven structural properties, with
100 cases each under the current runner defaults:

- Sorted helpers agree with simple list algorithms.
- Optimized interval/face answers agree with frozen pre-optimization oracles.
- Term renaming identity.
- Term substitution identity and composition.
- Weakening followed by instantiation.
- Interval reversal involution.
- De Morgan's meet/reversal law.
- Endpoint extraction commuting with substitution.
- Opposite endpoint faces are disjoint.

Term generators construct Fin-bounded indices and extend scopes under binders.
Shrinking retains scope because generator types retain the index bounds.
These terms are not necessarily well typed; they must not be used to claim
typed preservation or checker completeness.

Term nesting is capped at 4 (3 for composition), replacements at 2, and interval
nesting at 3 to limit normal-form growth. These caps are engineering limits,
not guarantees about elapsed time.

Independent constructor children use applicative composition; dependent
generators use explicit scope parameters. We do not filter random raw syntax
until it happens to type-check.

## Constructively generated erased typing

[Tests.TypedProperties](../test/src/Tests/TypedProperties.idr) adds five properties
with 100 cases each:

- Weak-head exposure agrees with full normal forms on the bounded typed corpus.
- Constructed term/type pairs are accepted.
- One beta step preserves checking against the supplied type.
- A typed identity application remains beta-convertible to its argument.
- Replacing the expected type with too-small Type 0 is rejected (higher universes
  are now compatible with universe-valued samples).

Generation starts with two universes and a polymorphic identity, then recursively
adds constant lambdas or identity applications. Expected types are constructed
alongside terms, not obtained by calling the checker as a generation oracle.
Mapping each wrapper over the whole pair preserves this relationship during
shrinking. This is a generator-side recipe, not a formal derivation certificate.

Depth is capped at 3; checker depth/reduction budgets are 100. All exhaustion is
a test failure, not a discarded case. Classification reports root applications,
lambdas, and reducible versus already-normal inputs; no minimum coverage
threshold is enforced yet.

This narrow closed-term grammar does not cover arbitrary dependent contexts,
all substitutions, or runtime resource usage. In particular, erased lambdas may
discard linear inputs; they must not be reused as runtime-valid samples.

## Constructive runtime properties

[Tests.RuntimeProperties](../test/src/Tests/RuntimeProperties.idr) adds five
properties (100 cases each) over the open context A : Type0 (erased), x : A
(linear). Starting from x, generation adds erased constant lambdas that capture
x and linear identity applications. Each sample carries a constructed type.

The suite checks:

- Generated terms are accepted with usage [1, 0].
- One beta step preserves their type and that usage.
- Bounded normalization preserves their type and that usage.
- Passing a sample to an unrestricted binder is rejected as duplication.
- Changing the input binder to erased rejects runtime extraction.

Generator depth is 4; checking and reduction budgets are 100. Shrinking maps
whole term/type pairs, preserving the construction relationship. Classification
reports reducible versus normal samples.

This covers a narrow, fixed dependent context and selected ordinary wrappers,
not arbitrary runtime derivations or cubical resource rules. The unrestricted
mutation is intentionally rejected even if its body uses its input once:
the caller obeys the declared argument quantity, not an optimization guess.

The default suite now runs 26 properties / 2,600 generated cases, alongside
deterministic regressions. Sampling counts are not proof coverage.

## Reproducing failures

Keep the failing property's name, shrunk input, reported size, seed, toolchain,
and pack collection. Hedgehog prints a recheck expression on failure. Load
the relevant file in `test/src/Tests/` (`Properties.idr`, `TypedProperties.idr`,
or `RuntimeProperties.idr`) in a pack-managed REPL and use that expression
in the module's scope. The runProperties wrapper does not currently expose
a command-line seed option.

Promote every discovered bug's smallest useful counterexample into a deterministic
regression, so coverage does not depend on random discovery again.

## Limits and next steps

Passing sampled properties is not a proof of soundness or algorithm correctness.
Coverage thresholds, general typed-derivation generators, independent oracle
comparisons beyond the frozen solver oracles, and shrinking-quality regression
tests are not yet implemented. Composition tests
currently use one bounded scope/replacement shape, not every possible telescope.

Next: expand generators to dependent open contexts and general substitutions,
and add enforced coverage and independent-oracle checks. Keep impossible
or exhausted evaluations distinct from rejected typing obligations.
