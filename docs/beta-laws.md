# Instantiation and root beta-step laws

Status: total Idris 2 proofs for raw scoped syntax and the actual root beta
clause of Reduction.step. These are not typed subject-reduction results.

## Instantiation naturality

[Core.Substitution.Instantiation](../src/Fibril/Core/Substitution/Instantiation.idr)
proves two identities for arbitrary scopes, maps, replacement values, and bodies:

    rename env (instantiateTerm value body)
      = instantiateTerm (rename env value) (rename (liftRenaming env) body)

    substituteTerm sigma (instantiateTerm value body)
      = instantiateTerm (substituteTerm sigma value)
                        (substituteTerm (liftSubstitution sigma) body)

The body starts with one additional variable. Transforming it uses a lifted map;
transforming the replacement value does not introduce that binder.

Both proofs expand instantiation through the **actual** replaceNewest map and use
[composition/fusion](substitution-composition.md), plus pointwise congruence.
For the newly removed variable, replacement maps compute identically. For an
older variable, the substitution proof uses instantiateWeakening to cancel the
shifted replacement. No equality of functions is postulated.

## The actual root beta step

[Core.Reduction.Beta](../src/Fibril/Core/Reduction/Beta.idr) proves:

    step (rename env (Apply (Lambda q domain body) argument))
      = Just (rename env (instantiateTerm argument body))

    step (substituteTerm sigma (Apply (Lambda q domain body) argument))
      = Just (substituteTerm sigma (instantiateTerm argument body))

These statements mention [Reduction.step](../src/Fibril/Core/Reduction.idr),
not a separately invented reduction relation. Renaming/substitution preserve the
root lambda/application shape, and the instantiation identities identify the
resulting contractum. The beta proofs are short congruence corollaries.

![Compatibility square for a known root beta redex](diagrams/beta-laws.svg)

## Why not claim arbitrary step commutation?

Substitution can create a beta redex where none existed:

    v0 ()                     -- neutral: no step
    substitute v0 := lambda   -- now a beta redex

It can also introduce a root redex before the argument redex the original
leftmost strategy would have selected. Thus the naive equation

    step (substituteTerm sigma term)
      = map (substituteTerm sigma) (step term)

is false in general. The proof requires a **known root beta redex**; it does not
quietly extend to arbitrary terms or evaluator strategy compatibility.

## Validation and trust boundary

[Tests.Beta](../test/src/Tests/Beta.idr) instantiates both naturality and root-step
theorems with nested binders, free/nonvariable replacements, and changing scopes.
It also retains both counterexamples to the overly broad step equation.

Proof modules are checked by Idris 2 under %default total, without holes,
postulates, function-extensionality axioms, unsafe casts, or totality escape
hatches. They are not imported by the checking/reduction services, and do not
change source syntax, budgets, or operational rules.

Nothing here proves typing/resource preservation, arbitrary contextual reduction
compatibility, confluence, normalization, canonicity, erasure, or cubical behavior.
[DEBRUIJN72](references.md#debruijn72) is background; these are our own proofs over
the implemented syntax and reducer. Fibril itself does not yet check these proofs.
