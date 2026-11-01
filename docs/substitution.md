# Basic structural substitution laws

Status: total Idris 2 proofs over every current Term constructor. This is not a
typed substitution theorem or a proof checked by Fibril.

## What is now proved

[Core.Substitution](../src/Fibril/Core/Substitution.idr) exports:

| Theorem | Statement |
| --- | --- |
| substituteCongruent | Pointwise equal replacements yield equal substituted terms. |
| renameAsSubstitution | rename env term = substituteTerm (Variable . env) term |
| substituteIdentity | substituteTerm Variable term = term |

All scopes, replacement syntax, and binder quantities are arbitrary. Neither
the term nor its replacements need to be well typed. The variable map used for
renaming need not be injective.

These are identities in the host's propositional equality. They do not add
Fibril equality reflection, new conversion rules, or cubical paths.

## Lifting through a binder

Substitution maps references to terms, not just other references. Under a binder:

    liftSubstitution sigma FZ     = Variable FZ
    liftSubstitution sigma (FS i) = weaken (sigma i)

![The old variables are weakened; the fresh variable stays fresh](diagrams/substitution.svg)

The congruence proof handles FZ by reflexivity. At FS i it applies congruence
of weaken to the assumed replacement equality. Structural induction then
extends this pointwise agreement through terms. Pi/Lambda annotations use the
original maps; their bodies use the lifted maps.

For renameAsSubstitution, the corresponding lifted maps agree pointwise:

    Variable (liftRenaming env i)
      = liftSubstitution (Variable . env) i

The fresh-variable and older-variable cases both compute by reflexivity.
The binder induction uses substituteCongruent rather than assuming equality
of functions or a function-extensionality axiom.

## Reuse the renaming theorem

Identity substitution is a corollary rather than another duplicated induction:

    substituteTerm Variable term
      = rename id term
      = term

The first equality is the symmetric variable-correspondence theorem; the second
is [renameIdentity](renaming.md). This keeps the proof dependencies explicit.

## Validation

[Tests.Substitution](../test/src/Tests/Substitution.idr) instantiates all public
theorem signatures. A concrete replacement with a free variable is substituted
through a lambda and Boolean/Unit case structure: the annotation keeps the old
scope, the new bound variable remains FZ, and the replacement's free reference
becomes FS FZ in the body. A host equality witness checks that exact result.

The package checks proofs under %default total, with no holes, postulates,
unsafe casts, or totality escape hatches. Existing Hedgehog properties remain
operational regressions; this adds no new randomized-property count.

## Still unproved

Full substitution composition, mixed renaming/substitution fusion, and general
weakening/instantiation laws remain future proofs. Their existing sampled tests
are not a substitute for those theorems. In particular, nothing here establishes
typed substitution, quantitative permissions under substitution, beta
preservation, normalization, erasure correctness, or cubical soundness.

[DEBRUIJN72](references.md#debruijn72) is binding background; these are our own
proofs over the concrete Term operations, not proofs transferred from a citation.
