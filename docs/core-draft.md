# Initial term core and quantity rules

Status: proposal for implementation. Not a completed calculus or soundness proof.

## Staging and trust

Implement a deliberately small ordinary dependent-function fragment before
connecting it to cubical terms. This fragment is a stepping stone, not a claim
that CCHM plus these quantities is sound.

Keep dimension contexts and term contexts separate. Existing restriction
contexts hold face assumptions only. No general recursion, partial definitions,
axioms, or unsafe primitives enter this initial logical fragment.

## Proposed initial grammar

    Level ::= natural number
    Term  ::= Var index
            | Universe Level
            | Pi Quantity Term Term
            | Lam Quantity Term Term
            | App Term Term

Indices are de Bruijn indices; 0 is the newest term variable. Pi and Lam bodies
extend the term scope; their domain annotations do not. Domain annotations on
lambdas simplify explicit core checking before surface inference exists.

Universe levels initially are literal natural numbers, with Type l : Type (l+1)
and Pi formation at max of domain/codomain levels. No Type : Type. Cumulativity,
level polymorphism, and impredicativity are not implicitly included.

Core syntax, substitution, evaluation, conversion, and typing must each receive
tests. Representation alone is not a checker.

## Proposed quantity accounting

Coefficients are 0, 1, and omega (unrestricted):

- Addition: 0 is identity; any sum of two nonzero coefficients is omega.
- Multiplication: 0 annihilates; 1 is identity; omega times omega is omega.
- A usage vector records computational use of each term variable.
- A variable contributes 1 at its position and 0 elsewhere.
- Application combines function usage with argument usage scaled by the
  function binder quantity: usage(f) + q * usage(argument).
- A lambda checks the usage of its bound variable, then returns the remaining
  usage vector for its closure.
- Binder 0 requires observed computational usage 0.
- Binder 1 requires observed usage exactly 1.
- Unrestricted binders permit any observed coefficient.

Quantity.idr implements coefficient arithmetic and this local binder policy.
It does not implement context checking, branch joining, erasure, or normalization.

Type annotations and types must be checked in a separate erased judgment:
references there do not consume runtime resources. The exact judgment and its
interaction with dependence and substitution must be specified before coding
the checker. Checking annotations twice must not accidentally count two uses.

An erased argument still needs checking. Erasure never licenses arbitrary
untyped terms. Conversely, a runtime term must not extract erased information.

## Required negative tests

- Discarding a linear binder in a computational body.
- Duplicating a linear variable.
- Returning an erased variable at runtime.
- Capturing a linear value in a closure and then duplicating that closure.
- Out-of-scope indices, including in annotations.
- Self-application through an inconsistent universe rule.
- A looping definition admitted as evidence of Void.

Some tests require later syntax; record them now rather than pretending they
are already executable.

## Cubical gate

Do not extend the ordinary application formula blindly to paths, composition,
or Glue. Specify separately:

- Which dimension operations are computationally erased.
- How boundary checking avoids falsely consuming resources multiple times.
- How composition systems account for overlapping and disjoint faces.
- How substitution and reduction preserve exact use.
- Which transport computations remain after erasure.

Until those obligations are addressed, describe this work as an experimental
ordinary quantitative fragment beside cubical infrastructure, not a finished
quantitative cubical kernel.

## Immediate next task

Implement scope-indexed term syntax and structural renaming/substitution for
the proposed grammar. Then build the erased/type-checking judgment explicitly
before implementing bidirectional checking.
