# Testing Fibril

## Layers

1. Deterministic regressions: explicit positive/negative examples, including
   erasure policy, scope checks, beta budgets, and erased checker failures.
2. Hedgehog properties: randomized structural laws with integrated shrinking.
3. Runnable bootstrap examples and generated handbook/API checks.
4. Future formal proofs and broader differential/typed-generation tests.

Run `make test` or `pack test fibril`. Both deterministic checks and properties
must pass; a failure exits nonzero. Run `make examples` and `make handbook`
when completing a documented task.

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

[Tests.Properties](../test/src/Tests/Properties.idr) runs eight structural properties, with
100 cases each under the current runner defaults:

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

[Tests.TypedProperties](../test/src/Tests/TypedProperties.idr) adds four properties
with 100 cases each:

- Constructed term/type pairs are accepted.
- One beta step preserves checking against the supplied type.
- A typed identity application remains beta-convertible to its argument.
- Replacing the expected type with a deliberately wrong universe is rejected.

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

## Reproducing failures

Keep the failing property's name, shrunk input, reported size, seed, toolchain,
and pack collection. Hedgehog prints a recheck expression on failure. Load
`test/src/Tests/Properties.idr` (or `TypedProperties.idr`) in a pack-managed REPL and use that expression
in the module's scope. The runProperties wrapper does not currently expose
a command-line seed option.

Promote every discovered bug's smallest useful counterexample into a deterministic
regression, so coverage does not depend on random discovery again.

## Limits and next steps

Passing sampled properties is not a proof of soundness or algorithm correctness.
Coverage thresholds, general typed-derivation generators, independent oracle
comparisons, and shrinking-quality regression tests are not yet implemented. Composition tests
currently use one bounded scope/replacement shape, not every possible telescope.

Next: expand generators to dependent open contexts and general substitutions,
and add enforced coverage and independent-oracle checks. Keep impossible
or exhausted evaluations distinct from rejected typing obligations.
