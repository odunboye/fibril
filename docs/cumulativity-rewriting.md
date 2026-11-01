# Cumulativity and dependent rewriting

Status: staged design. Literal-level compatibility is the next implementation
step; symbolic levels, constructor propagation, and dependent rewriting are not
implemented. This is not a soundness proof of a quantitative cubical extension.

## Universe cumulativity, not equality

Intended rule: if A : Type i and i <= j, A may be checked at Type j.
This must not make Type i definitionally equal to Type j.

Separate:

- Conversion: computational equality under specified rules.
- Compatibility: directional acceptance of an inferred type at an expected type.

## Implementation sequence

1. Literal-level compatibility: normalize inferred/expected types; permit
   Universe i at Universe j when i <= j; otherwise require existing beta equality.
2. Use compatibility for argument/checking obligations, not for the conversion API.
3. Specify constructor propagation separately. Initially Pi domains, quantities,
   and codomains remain invariant; no function subtyping is inferred.
4. Add level variables, successor/max expressions, and inequality constraints.
5. Justify interactions with cubical paths, composition, Glue, and universes.

Literal compatibility alone is not a complete cumulative dependent type theory.
In particular, Pi codomain covariance and substitution/preservation need explicit
rules. Do not advertise general subtyping or infer the consistency of the combined
system from an ordinary universe rule.

## Tests required

- Checking into a larger literal universe succeeds.
- Checking down a universe and Type : Type fail.
- Equal and distinct universe conversion outcomes remain unchanged.
- Beta-reduced universe compatibility works.
- Exhaustion remains inconclusive/failure.
- Pi domains/quantities do not silently coerce.
- Symbolic levels/cubical rules are not assumed.

## Dependent rewriting is transport

Illustrative, not finalized syntax:

    p : Path A x y
    P : A -> Type
    value : P x
    transport P p value : P y

Changing an index changes the types of its dependent values. In a context
x : A, v : P x, w : Q x v, moving x to y requires transporting v and adjusting
w relative to the transported value. Textual name replacement is insufficient.

## Rewriting sequence

1. Specify and implement paths, dependent paths, and cubical transport.
2. Establish the selected computation/boundary rules.
3. Offer explicit transport terms.
4. Add rewrite elaboration producing ordinary checked terms.
5. Add occurrence selection, reverse rewriting, and dependency-aware context rewriting.
6. Add controlled simplification after primitives are reliable.

No rewrite tactic or transport primitive is implemented yet.

## Safeguards

- No equality reflection: a path is not automatic definitional equality.
- No blanket uniqueness/irrelevance of paths.
- Computationally relevant transport must survive justified erasure.
- Rewriting must respect quantities and not duplicate linear resources.
- Automation constructs terms; it does not enlarge kernel trust.
- Cumulativity does not grant coercions between merely equivalent types.

## References

[CCHM18](references.md#cchm18) is the cubical starting point;
[HOTT13](references.md#hott13), ch. 2, explains transport/path reasoning;
[ATKEY18](references.md#atkey18) motivates quantitative substitution obligations.
None automatically proves these proposed extensions sound. Record the exact
cumulative cubical rules before implementing the full foundation.
