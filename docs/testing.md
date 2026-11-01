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

[Tests.Properties](../test/src/Tests/Properties.idr) runs eight properties, with
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

## Reproducing failures

Keep the failing property's name, shrunk input, reported size, seed, toolchain,
and pack collection. Hedgehog prints a recheck expression on failure. Load
`test/src/Tests/Properties.idr` in a pack-managed REPL and use that expression
in the module's scope. The runProperties wrapper does not currently expose
a command-line seed option.

Promote every discovered bug's smallest useful counterexample into a deterministic
regression, so coverage does not depend on random discovery again.

## Limits and next steps

Passing sampled properties is not a proof of soundness or algorithm correctness.
Coverage thresholds, typed-term generators, independent oracle comparisons, and
shrinking-quality regression tests are not yet implemented. Composition tests
currently use one bounded scope/replacement shape, not every possible telescope.

Next: expand scoped/typed generator coverage, record classifications, and test
the ordinary checker's substitution/conversion relationships. Keep impossible
or exhausted evaluations distinct from rejected typing obligations.
