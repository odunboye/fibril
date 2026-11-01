# Foundation baseline: De Morgan cubical type theory

Status: selected reference for initial engineering, not a completed Fibril calculus.

See the [code-to-theory map](references.md#code-to-theory-map) for per-module
correspondences and the limits of each citation. Quantity integration additionally
requires [ATKEY18](references.md#atkey18); neither reference establishes the
soundness of their combination.

## Reference

Cyril Cohen, Thierry Coquand, Simon Huber, Anders Mörtberg,
*Cubical Type Theory: a constructive interpretation of the univalence axiom*,
Logical Methods in Computer Science 14(4), 2018.

- https://doi.org/10.23638/LMCS-14(4:5)2018
- https://arxiv.org/abs/1611.02108

Use the published CCHM presentation as the baseline for interval expressions,
face restrictions, paths, composition, and Glue. Record any adopted later
refinements explicitly. Do not silently combine rules from different systems.

## First implemented fragment

Interval syntax with endpoints, variables, meet, join, and reversal; structural
substitution; interpretation under Boolean endpoint assignments.

Symbolic interval equality is implemented separately in NormalForm.idr using
absorbed disjunctive normal forms of signed generators. Reversal is pushed to
generators using De Morgan laws. Complementary literals are not cancelled.
This reference algorithm can grow exponentially; it is not a performance claim
or a formal proof of correctness.

Face.idr separately implements face formulas, equality, and entailment using
consistent absorbed DNF clauses. Opposite endpoints are disjoint, but their join
is not Top. Entailment checks that each premise clause contains a conclusion
clause. This is a reference algorithm with potentially exponential growth;
formal verification and broader property testing remain open.

Endpoint extraction now maps interval expressions to faces using De Morgan
endpoint rules. Face substitution replaces dimension names by interval
expressions. Tests check endpoint/substitution compatibility and endpoint
disjointness over a small generated corpus; these are not formal proofs.

Scope.idr adds dimension-count-indexed intervals and faces with Fin indices,
checked conversion from raw Nat-labelled syntax, interval weakening, scoped
substitution, and instantiation of the newest dimension. Index 0 denotes the
newest dimension. Raw validation checks even algebraically redundant branches,
so simplification cannot hide invalid references. Scoped face entailment reuses
the reference solver after forgetting indices. Scoped face substitution, weakening, and instantiation now preserve scope
through endpoint extraction. Restriction.idr accumulates face assumptions and
checks entailment under them, including empty (contradictory) faces. These are
dimension restrictions, not term contexts or arbitrary logical assumptions.
No term binding or computational-variable usage rules exist yet.

These structures are not yet integrated with term typing. There is no
term conversion procedure, universe checking, composition, or Glue.

The interval is a free De Morgan algebra, not a Boolean algebra. In particular,
do not add the general equations i ∨ ~i = 1 or i ∧ ~i = 0. Checking all Boolean
vertices loses this distinction and must never serve as conversion checking.

The face lattice is a separate structure. Do not identify interval expressions,
face predicates, or runtime Bool values.

## Quantitative extension: unresolved

CCHM itself does not supply Fibril's exact-use linear resource system.

Before adding quantitative cubical typing, specify:

- Separate dimension/face contexts from computational variable usage.
- Quantity annotations on binders and usage accounting under substitution.
- Usage in types versus computationally relevant term occurrences.
- Whether path boundaries are checking obligations or computational uses.
- How composition systems and Glue preserve exact-use resources.
- Which transport operations survive erasure.
- Subject reduction and substitution obligations for the combined system.

These are obligations, not established rules. Do not label an experimental
checker a sound quantitative cubical theory without supporting arguments.

## Next implementation gates

1. Symbolic interval equality: implemented with law/regression tests; formal verification and broader property testing remain open.
2. Face syntax, entailment, scoped substitution, and restriction contexts: implemented with regression tests. Term contexts remain open.
3. A documented core grammar, contexts, universes, and ordinary typing rules.
4. Path checking and evaluation, with quantities gated on explicit rules.
5. Composition, Glue, and a computational univalence example.

The scope/order may change if the selected calculus requires a more integrated
implementation. No consistency or normalization claim is made here.
