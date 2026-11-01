# Theoretical references and implementation correspondence

References explain provenance and intended foundations. **Citing a paper does
not transfer its soundness results to Fibril.** Our combined quantitative cubical
calculus is still unresolved; no full checker or correctness proof exists.

## Code-to-theory map

| Code | Reference | What corresponds | What is not established |
| --- | --- | --- | --- |
| [Quantity](../src/Fibril/Core/Quantity.idr) | ATKEY18 §2.1.1; MCBRIDE16 | Zero/one/many semiring and erased-versus-computational usage | The local allows policy is not a complete QTT judgment or justified subusage relation |
| [Term](../src/Fibril/Core/Term.idr) | DEBRUIJN72; ATKEY18 §2 | Nameless bound variables, lifted substitution, quantity-annotated dependent functions | No typing, conversion, or preservation theorem; our syntax is not a verbatim QTT presentation |
| [Interval](../src/Fibril/Foundation/DeMorgan/Interval.idr) | CCHM18, interval algebra presentation | Free De Morgan interval, reversal, meet/join, dimension substitution | Boolean vertex evaluation is not interval equality |
| [NormalForm](../src/Fibril/Foundation/DeMorgan/NormalForm.idr) | CCHM18, free De Morgan algebra | Equality respects distributivity, absorption, involution, and De Morgan laws | Our absorbed-DNF algorithm is an implementation choice, not code or a verified algorithm taken from the paper |
| [Face](../src/Fibril/Foundation/DeMorgan/Face.idr) | CCHM18, face lattice and restricted judgments | Endpoint constraints, disjoint endpoints, restrictions, endpoint substitution | DNF solver correctness has tests, not a formal proof |
| [Scope](../src/Fibril/Foundation/DeMorgan/Scope.idr) | DEBRUIJN72; CCHM18 dimension contexts | Fin-bounded indices and dimension reindexing | Scope indices alone establish neither typing nor resource safety |
| [Restriction](../src/Fibril/Foundation/DeMorgan/Restriction.idr) | CCHM18, face-restricted contexts | Accumulated face assumptions and entailment | Not a full cubical context or arbitrary theorem assumptions |
| [Proof examples](../examples/README.md) | HOTT13 ch. 1; Idris 2 implementation | Dependent functions, indexed data, induction, equality proofs | Executed/checked by Idris 2, not by Fibril |

## CCHM18

Cyril Cohen, Thierry Coquand, Simon Huber, Anders Mörtberg.
*Cubical Type Theory: a constructive interpretation of the univalence axiom.*
Logical Methods in Computer Science 14(4), 2018.

- [Published version](https://doi.org/10.23638/LMCS-14(4:5)2018)
- [Preprint](https://arxiv.org/abs/1611.02108)

Read the presentations of the interval algebra, face lattice, restricted
contexts, paths, composition, and Glue. Use the published version as our baseline;
section numbering can differ between versions.

Implemented: algebra/scoping infrastructure only. Composition, Glue, path term
checking, universe checking, and computational univalence remain future work.
Our proposed quantity system is an additional design, not a CCHM result.

## ATKEY18

Robert Atkey. *Syntax and Semantics of Quantitative Type Theory.*
LICS 2018, pp. 56–65.

- [DOI](https://doi.org/10.1145/3209108.3209189)
- [Author's paper](https://bentnib.org/quantitative-type-theory.pdf)

Relevant reading:

- §2.1.1: usage semirings, including zero/one/many, positivity, and zero-product.
- §2.1.3: contexts, erased/present judgments, dependent function rules.
- §2.2: zeroing, weakening, and substitution properties.
- §2.3: why a seemingly reasonable earlier formulation fails substitution.

This is a warning against deriving a checker from coefficient arithmetic alone.
Before implementing typing, explicitly account for erased/present modes and
substitution. Fibril's allows helper is an experimental local policy; it must
not be mistaken for the paper's complete rules.

## MCBRIDE16

Conor McBride. *I Got Plenty o' Nuttin'.*
In *A List of Successes That Can Change the World*, LNCS 9600,
2016, pp. 207–233.

- [DOI](https://doi.org/10.1007/978-3-319-30936-1_12)

Historical motivation for combining dependence with resource annotations:
information may occur in types without being consumed at runtime. Read alongside
Atkey's subsequent correction concerning substitution; do not combine their
rules indiscriminately.

## DEBRUIJN72

N. G. de Bruijn. *Lambda calculus notation with nameless dummies, a tool for
automatic formula manipulation, with application to the Church–Rosser theorem.*
Indagationes Mathematicae (Proceedings) 75(5), 1972, pp. 381–392.

- [DOI](https://doi.org/10.1016/1385-7258(72)90034-0)

Background for nameless indices and binder manipulation. Fibril's Fin-indexed
Idris encoding and helper functions are our implementation choices; this citation
does not claim that the paper supplies this exact dependently typed encoding.

## HOTT13

The Univalent Foundations Program. *Homotopy Type Theory: Univalent Foundations
of Mathematics.* Institute for Advanced Study, 2013.

- [Book and downloads](https://homotopytypetheory.org/book/)

Background reading: ch. 1 for dependent type theory; ch. 2 for paths,
equivalences, and univalence; ch. 6 for higher inductive types. This is conceptual
background, not the computational specification of our cubical kernel.

## IDRIS2

Edwin Brady. *Idris 2: Quantitative Type Theory in Practice.*
ECOOP 2021, LIPIcs 194, article 9.

- [DOI](https://doi.org/10.4230/LIPIcs.ECOOP.2021.9)
- [Idris 2 documentation](https://idris2.readthedocs.io/en/latest/)

Reference for practical quantities and the host implementation language.
Pinned bootstrap revisions are recorded in the project README and pack.toml.
Idris-like syntax does not establish that our future cubical equality behaves
exactly like Idris equality.

## Reference maintenance

Use these stable keys in source comments and link relevant sections from design
pages. Explain whether a reference is a selected calculus, an algorithm source,
or background inspiration. Identify departures and unresolved proof obligations.
When implementing a new rule, cite the specific rule/section after checking it;
do not invent theorem correspondences from a title or abstract.
