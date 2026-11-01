# 6. Cubical coordinates and boundary logic

## Learning goals

Separate intervals from faces, explain dimension scoping, and identify the
missing step from algebra infrastructure to computational univalence.

## Interval expressions are not Bool

[Interval](../../src/Fibril/Foundation/DeMorgan/Interval.idr) represents endpoints,
variables, meet, join, and reversal in a free De Morgan algebra.

    reverse (meet i j) = join (reverse i) (reverse j)

But i join reverse i is not generally 1. Testing only assignments of endpoints
to variables would incorrectly collapse this distinction into Boolean algebra.

[NormalForm](../../src/Fibril/Foundation/DeMorgan/NormalForm.idr) pushes reversal
to signed generators and uses absorbed disjunctive normal forms. It does not
cancel complementary literals. This reference algorithm can grow exponentially.

### Optimize representation, not the algebra

[Sorted](../../src/Fibril/Foundation/DeMorgan/Sorted.idr) exploits canonical list
order: adjacent duplicates can be removed in one pass, and subset checking can
merge two sorted lists. The old algorithms remain test oracles. Local
[measurements](../benchmarks.md) show lower overhead, not a cure for DNF expansion.
Always preserve the non-Boolean algebra while changing implementation details.

## Faces describe where an obligation holds

[Face](../../src/Fibril/Foundation/DeMorgan/Face.idr) is a separate lattice.
Endpoint i false means the face where i is 0.

    (i = 0) AND (i = 1) = Bottom
    (i = 0) OR  (i = 1) != Top

The first is impossible; the second describes a boundary, not the entire cube.

Entailment reduces formulas to consistent absorbed clauses. Each premise clause
must include a conclusion clause. This is our implementation strategy, not a
machine-checked proof of solver correctness.

## Extract endpoints and substitute

For a meet to be 1, both factors must be 1. For it to be 0, either may be 0.
Joins have the dual rule; reversal swaps endpoints.

substituteFace replaces dimension names by interval expressions and extracts their
appropriate endpoint conditions. This is not ordinary Boolean evaluation.

## Keep dimensions in scope

[Scope](../../src/Fibril/Foundation/DeMorgan/Scope.idr) uses Fin indices for
dimensions, like chapter 2 does for computational variables. The two contexts
remain distinct. Even redundant raw expressions are scope checked before they
can hide invalid references behind simplification.

[Restriction](../../src/Fibril/Foundation/DeMorgan/Restriction.idr) accumulates
face assumptions. A contradictory restriction denotes an empty face. Obligations
there are vacuous; this does not authorize arbitrary global proofs.

## What is still missing?

Paths as term constructors, restricted term equality, composition, Glue,
universe rules for the cubical core, and justified quantitative interactions.
Univalence is a goal, not an existing primitive in our checker.

## Exercise

Why is cancelling i meet reverse i to 0 incorrect in Interval, while conjoining
its opposite endpoint constraints gives Bottom in Face?

**Theory:** [CCHM18](../references.md#cchm18).
**Read:** [foundation baseline](../foundation-baseline.md).
