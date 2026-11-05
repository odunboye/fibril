# Import and name-resolution roadmap

Status: working plan for the `feature/unqualified-imports` worktree. The
unqualified-direct-import prototype exists in this worktree but is not merged.
Import qualifier aliases, selective imports, and bounded public re-exports have
prototypes in this worktree; type-directed name resolution remains a proposal. This roadmap is
not a claim of Idris 2 compatibility or semantic equivalence.

## Goals

Make common imported names concise, while making resolution predictable,
inspectable, bounded, and consistent across compiler and editor services.
Checked module interfaces and the independent core checker remain authoritative.
No import may expose a private or erased definition as a runtime value, add a
transitive dependency without permission, or turn an exhausted check into
success. Existing qualified calls remain a stable escape hatch.

## Current worktree prototype

Direct checked exports receive an unqualified alias only when unique. Qualified
references remain available. Lexical/local bindings shadow imports; imported
names shadow the bundled Prelude. Colliding imported names require a qualifier.
The prototype covers ordinary references, implicit metadata, direct data
patterns, imported interface schemas, and single-root project definition
navigation. Selective imports restrict visibility to named checked exports.
Public imports require explicit selections. Re-exported interface schemas retain
constructor origins; method-block construction requires the matching constructor
to be selected. Single-root project definition navigation uses checked canonical
identities for public exports and returns no target when an origin cannot be
located. The package CLI supports checked application graphs; standalone library
inventory navigation and package-aware editor integration remain unimplemented.
Qualified-only imports and project-wide references/rename also remain future work.

Evidence: after the interface-origin fix, the isolated `make -j8 test` passed
compiler/property checks, 140 CLI tests and 9 native tests; 32 focused import
checks, 5 editor tests and 16 handbook tests also passed. A prior full CLI run
timed out after 91 tests before the successful retry. Build-dependent tests are
serialized after a parallel build/test attempt left an incomplete executable.
An earlier intermittent primitive-check failure did not recur; its cause remains
unconfirmed. This is regression evidence, not a proof, and must be repeated on
the final commit.

## Phase 0 — settle and review the prototype

- Specify exact precedence across lexical binders, earlier local declarations,
  directly imported names, current-module qualified names and the Prelude.
- Confirm the policy intentionally differs from Idris 2's type-directed
  disambiguation. Import order must never silently choose among collisions.
- Audit aliasing against erased globals, implicit arguments, providers,
  constructors, schemas, quotas, and admission cost. Preserve canonical
  identities; aliases must not duplicate instance/provider registrations.
- Review the complexity of candidate collection and enforce existing resource
  bounds; do not introduce unbounded pairwise work for large export sets.
- Test unique names, ambiguity, qualification, local/Prelude shadowing,
  private and transitive invisibility, imported constructors (including implicit
  parameters), implementation schemas, erased usage, package boundaries,
  explicit dictionary/provider selection, source order, and editor navigation.
- Ensure diagnostics identify colliding fully qualified names and source spans.
- Run unit/property, complete CLI, editor, native, and handbook checks; update
  status descriptions consistently. Commit this phase before building on it.

Acceptance: a checked, reviewed direct-import feature with no change to private,
quantity, graph or core checking rules. Named imports that do not occur must not
fail just because two dependencies export the same name.

## Phase 1 — explicit import control

The worktree implements `import App.Greeting as Greeting` and nonempty exact
selectors such as `import App.Greeting (greet)`. The original qualifier remains
available for selected names. Selecting a type does not select constructors or
helpers. A qualified-only form remains a proposal; do not assume Idris supports
Fibril's selective-import syntax. See [modules](modules.md) for the current
prototype's precise visibility, collision and interface-constructor rules.

Implementation must retain authored source spans, update graph metadata and
package ownership, install only checked exports, and apply the same scope rules
in ordinary expressions, patterns, schemas, inference, diagnostics and editor
services. Include parser/formatter round trips and negative tests. Provide a
fully qualified spelling for every imported name.

## Phase 2 — deliberate public re-exports

A bounded selected-public-import prototype exists, including interface schemas
and checked definition navigation to original declarations in single-root and
application-package graphs. Remaining work includes standalone library inventory
and editor integration, references, rename and wider validation.
Further design must address visibility and the distinction between
re-exporting a name and revealing its definition for conversion. Track original
canonical identity and provenance through direct imports and multiple re-export
paths; deduplicate identical origins and diagnose genuinely distinct ones.
Respect package direct-dependency policy, private declarations, quantities,
provider metadata, source-order rules, cycles, and graph budgets. Define whether
qualified access follows the re-exporting or original module path, and how
collisions and aliases interact.

Tests must cover diamond imports, cycles, private/erased names, conflicting
re-exports, package boundaries, changed exports, provenance and navigation.
Re-export must not become implicit transitive visibility.

## Phase 3 — resolution explanation and editor parity

Expose a checked resolution result containing canonical target, provenance,
candidates, shadowing and source locations. Reuse one resolution policy between
checking and editor services rather than recomputing an approximate policy.
Design an `explain-name`/hover interface and clear ambiguity diagnostics. Keep
syntax-only navigation explicitly separate from checked project navigation.
Extend package-aware definition navigation and design project-wide references
and rename with snapshot identity and capture/conflict checks. Do not claim
safe cross-file rename before those checks exist.

## Phase 4 — optional bounded type-directed disambiguation

Only after explicit rules are stable, evaluate whether overload resolution is
worth its complexity. Specify its interaction with expected types, implicit
arguments, interface search, quantities, effects, and conversion. Candidate
checking must be transactional, bounded and deterministic. Zero candidates,
multiple valid candidates, and exhausted/inconclusive searches are distinct
errors; never select the first candidate or accept exhaustion as success.
Explicit qualification must always remain available.

Adding an export may introduce ambiguity or a new applicable candidate. Specify
and test stability guarantees rather than promising that type-directed choices
cannot change. Consider an opt-in strict policy for projects requiring explicit
selection on collisions.

## Phase 5 — policy and performance

Consider project settings for qualified-only or selective imports, collision
warnings, and stable dependency policies. Benchmark candidate resolution on
bounded wide/deep module graphs, including hostile collision sets, with a simple
reference implementation as an oracle. Limits are admission policies, not
proofs of time or memory bounds. Provide migration guidance for projects that
previously relied on a name being unbound.

## Completion and merge gates

For each phase: document actual syntax/status; include runnable positive and
negative examples; verify compiler, runtime staging, module/package isolation,
editor services and formatter; run the relevant suites plus full regressions;
review changes against the original worktree; and commit independently. Do not
merge uncommitted, unreviewed, or partially tested phases as a complete feature.
