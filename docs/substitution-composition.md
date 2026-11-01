# Structural substitution composition

Status: total Idris 2 proofs for every current Term constructor, including
arbitrary scopes, quantities, and replacement terms. No typing premise is assumed.

[Core.Substitution.Composition](../src/Fibril/Core/Substitution/Composition.idr)
builds on the [basic substitution](substitution.md) and [renaming](renaming.md)
laws without adding a reduction rule or a source-language feature.

## Theorems

Let sigma map source variables to intermediate terms, tau map intermediate
variables to final terms, and rho be a variable renaming.

| Theorem | Identity |
| --- | --- |
| renameAfterSubstitution | rename rho (substituteTerm sigma term) = substituteTerm (rename rho . sigma) term |
| substituteAfterRenaming | substituteTerm sigma (rename rho term) = substituteTerm (sigma . rho) term |
| substituteWeakening | substituteTerm (liftSubstitution sigma) (weaken term) = weaken (substituteTerm sigma term) |
| substituteComposition | substituteTerm tau (substituteTerm sigma term) = substituteTerm (substituteTerm tau . sigma) term |
| instantiateWeakening | instantiateTerm value (weaken term) = term |

Order matters: the composition theorem applies sigma first, then tau to every
replacement. The type indices enforce compatible intermediate scopes.

## The binder obstacle

A composition result cannot simply reuse the outer replacement map below a
binder: both substitutions must be lifted, preserving the fresh variable.

For the newest index the lifted composition computes to Variable FZ. For an
older index FS i, it must establish:

    substituteTerm (liftSubstitution tau) (weaken (sigma i))
      = weaken (substituteTerm tau (sigma i))

That is exactly substituteWeakening. Its proof combines the two mixed fusion
laws, not an assumption that substitution and weakening commute.

The first mixed law needs [renameWeakening](renaming.md) for the corresponding
older-variable case. Pointwise substituteCongruent then bridges the maps in
Pi/Lambda bodies. Annotations stay in the outer scope. Unit/Bool cases recurse
without introducing binders.

![Proof dependency order](diagrams/substitution-composition.svg)

Atoms compute by reflexivity. The remaining proofs are structural induction and
equality composition, without function extensionality, postulates, holes, unsafe
casts, or totality escape hatches.

## Instantiation uses the same replacement map

Term.replaceNewest factors out the existing map used by instantiateTerm:

    replaceNewest value FZ     = value
    replaceNewest value (FS i) = Variable i

This is the same replacement algorithm previously local to instantiateTerm,
not a new computation rule. Exposing the helper lets the theorem refer to the
actual map instead of duplicating an inaccessible local definition.

After weakening, substitution after renaming reaches only FS indices, whose
replacements are their original variables. substituteIdentity completes the
instantiation theorem. The replacement value is irrelevant because the removed
variable does not occur.

## Application: instantiation and beta

[Naturality/root-beta laws](beta-laws.md) now use these fusion/composition results
to commute renaming/substitution with instantiateTerm, then prove compatibility
of a known root beta contraction in the actual reducer. The broader equation
claiming arbitrary substitution commutes with the deterministic step strategy
is false and has explicit counterexample regressions.

## Evidence, tests, and limits

[Tests.SubstitutionComposition](../test/src/Tests/SubstitutionComposition.idr)
instantiates each public theorem with scope changes, non-variable/free
replacements, nested binders, and all current constructors. Existing randomized
composition and weakening/instantiation checks remain independent regressions;
those theorem-witness cases do not add randomized properties.

All results are **host equality of raw syntax**, checked by Idris 2, not Fibril.
They do not establish typed or quantitative substitution, reduction preservation,
confluence, normalization, canonicity, correct erasure, or cubical computation.
In particular, ordinary substitution composition is not cubical composition.

[DEBRUIJN72](references.md#debruijn72) is background for nameless binding.
These are our own proofs over the implemented operations, not theorem claims
borrowed from a citation.
