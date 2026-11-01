# Structural renaming laws

Status: implemented total Idris 2 proofs over all current Term constructors.
These are host-checked syntax theorems, not Fibril proofs or typing preservation.

## Operations and statements

[Term.rename](../src/Fibril/Core/Term.idr) maps Fin n references to Fin m,
lifting the map under Pi/Lambda bodies. Domain annotations stay outside that
binder. Unit/Bool cases introduce no binders.

[Core.Renaming](../src/Fibril/Core/Renaming.idr) proves:

| Theorem | Statement |
| --- | --- |
| renameCongruent | Pointwise agreement of maps implies equal renamed terms. |
| renameIdentity | rename id term = term |
| renameComposition | rename second (rename first term) = rename (second . first) term |
| renameWeakening | rename (liftRenaming env) (weaken term) = weaken (rename env term) |

Renaming maps need not be injective: variables may merge. All scopes and
quantities are arbitrary. Terms need not be well typed.

![Weakening commutes with lifted renaming](diagrams/renaming.svg)

## Why pointwise agreement matters

A lifted identity is not syntactically written id. Likewise, composing two
lifted maps is not syntactically written as lifting their composition.

We do not assume function extensionality to identify those functions. Instead,
liftAgreement lifts a proof at each Fin index, and renameCongruent uses
structural induction to lift that pointwise fact through the term.

The binder identity case, for example, rewrites:

1. The annotation using the recursive identity theorem.
2. The body map from lifted id to id using pointwise congruence.
3. The body term using the recursive identity theorem.

Composition follows the same pattern, using liftComposition at the body.
Atoms use reflexivity. Applications and Unit/Bool cases recurse into children;
they do not extend scope. The weakening corollary composes the general
composition/congruence results rather than duplicating induction.

## Evidence and trust boundary

These functions are checked under %default total. There are no holes,
postulates, unsafe casts, totality escape hatches, or function-extensionality
axioms in this module. Idris 2 equality, structural recursion, congruence, and
transitivity supply the host proof machinery.

The proof module is separate from Term and is not imported by checking or
reduction services. The package build type-checks it; it adds no source syntax,
runtime resource rule, normalization step, or checker budget.

The statements relate **raw scoped syntax** in Idris equality. They do not prove:

- formation or typing preservation under renaming;
- substitution composition or beta subject reduction;
- preservation of quantitative permissions;
- normalization, canonicity, or erasure correctness;
- cubical equality, paths, transport, or combined-foundation soundness.

[DEBRUIJN72](references.md#debruijn72) is binding background. The proofs over
Fibril's particular scoped datatype are our own implementation, not code or
specific theorem claims transferred from that reference.

## Regression coverage and next step

[Tests.Renaming](../test/src/Tests/Renaming.idr) instantiates all public laws in
nested scopes, with every constructor, an outer-variable swap, and a many-to-one
map followed by weakening. Existing Hedgehog structural properties remain useful
as independent operational regressions, but identity is no longer only sampled.

Future substitution laws can use renameWeakening to relate shifted replacement
terms under binders. That work must still address lifted substitutions explicitly;
these renaming theorems are not a substitute for proving those laws.
