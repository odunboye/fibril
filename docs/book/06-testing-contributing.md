# 7. Testing, evidence, and maintainable growth

## Learning goals

Choose the right test layer, understand constructive generators, and complete a
change without letting documentation or architecture drift.

## Three complementary kinds of evidence

- Deterministic tests preserve known examples and exact rejection behavior.
- Hedgehog properties explore bounded random structures and shrink failures.
- Formal proofs would establish general statements under explicit assumptions.

None substitutes for all the others. A passing sample suite is not a consistency
or preservation theorem.

## Generators should preserve the property being explored

Structural generators keep Fin indices in scope. Erased typing generators build
term/type pairs together from known constructions, without asking the checker to
filter arbitrary input or generate its own expected answer.

Runtime generators use a fixed context with an erased type and linear value.
They preserve one capture while building erased lambdas and linear identity
applications, then test reduction and invalid quantity mutations.

Shrinking must preserve the construction relationship. Applicative composition
helps independent parts shrink effectively.

## Reproduce and retain failures

Keep the shrunk term, property name, size, seed, toolchain, and package collection.
Use Hedgehog's reported recheck expression. Convert useful counterexamples into
deterministic regressions so later runs need not rediscover them.

The current suite has bounded grammars and classification reports, not complete
derivation coverage or enforced minimum coverage thresholds.

## A maintainability checklist

1. Give each module one clear responsibility.
2. Document public contracts, invariants, and unsupported cases.
3. Add abstractions only when real use demonstrates their value.
4. Keep kernel services independent of orchestration/editor code.
5. Update selected call graphs and theory correspondences with implementation.
6. Refactor duplication separately from adding new behavior.
7. Commit each meaningful tested task.

Run:

```sh
make test
make examples
make handbook
```

## Measure without weakening guarantees

The [safety/performance plan](../safety-performance.md) names current costs:
DNF growth, repeated checking, full normalization, and copying substitution.
Use the [reference benchmarks](../benchmarks.md) to collect raw timings and
metadata; establish stable baselines before optimizing or imposing thresholds. [Zig's lessons](../zig-lessons.md)
encourage explicit allocation/failure and readable resource contracts, without
making fast builds less trustworthy.

## Exercise the diagnostic boundary

[Diagnostic tests](../diagnostics.md) distinguish positional frontend failures
from unlocated core errors. Check CRLF, EOF and tabs as scalar positions; never
infer UTF-16 indices or terminal-cell widths from those columns. File drivers
preserve structured failures and add excerpts without rerunning the checker.

## Exercise

Propose a failing test that distinguishes an erased-valid function from a
runtime-invalid one. Which generator family should contain it?

**Read:** [testing guide](../testing.md),
[documentation policy](../documentation-policy.md),
[contributor checklist](../../CONTRIBUTING.md).
