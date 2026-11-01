# Theoretical references and implementation correspondence

References explain provenance and intended foundations. **Citing a paper does
not transfer its soundness results to Fibril.** Our combined quantitative cubical
calculus is still unresolved; only an erased ordinary prototype exists, not a
full checker or correctness proof.

## Code-to-theory map

The **application** column explains what we implement from the ideas; the
**purpose and role** column explains why Fibril needs it. Future uses are labeled
as intended rather than existing checker functionality.

| Code | Reference | Application: what we do with the theory | Purpose and role in Fibril | What is not established |
| --- | --- | --- | --- | --- |
| [Quantity](../src/Fibril/Core/Quantity.idr) | ATKEY18 §2.1.1; MCBRIDE16 | Represent erased, exact-once, and unrestricted usage; combine and scale coefficients using the zero/one/many semiring. | Resource-accounting foundation for intended linear checking and erasure: distinguish type-only information from runtime resources and detect duplication or discarding of linear inputs. | The local allows policy is not a complete QTT judgment or justified subusage relation; runtime checking now uses it experimentally, without a preservation proof. |
| [Runtime](../src/Fibril/Core/Runtime.idr) | ATKEY18 §2 | Combine erased typing with type-directed usage inference, binder discharge, and ambient validation. | Experimental resource checking for ordinary functions, including captured linear resources and erased arguments. | Conservative local subusage policy is not formally justified; no cubical checking, verified erasure, or backend runtime exists. |
| [Erased](../src/Fibril/Core/Erased.idr) | ATKEY18 §2.1.3; DEBRUIJN72 | Check context formation, universes, primitive Unit/Bool, Pi/lambda/application in erased mode using scoped substitution and beta comparison. | First experimental type-checking service for type-only ordinary terms; separates logical checking infrastructure from unresolved runtime usage rules. | No full QTT/CCHM implementation, runtime resource validation, cubical terms, or soundness proof. |
| [Alternative permissions](alternatives.md) | Finite local allows-policy design; not a rule taken verbatim from ATKEY18 | Define the least common permission; prove its admission identity by total case analysis in Idris 2 and lift it pointwise to vectors. | Admit alternative usages precisely when one permission admits both, without adding mutually exclusive paths. | The host-checked coefficient identity is not typed substitution, quantitative preservation, erasure correctness, or a cubical join theorem. |
| [Boolean rules](boolean.md) | HOTT13 ordinary-type background; explicit local policy | Bool : Type0, two constructors, conditional computation, equal branch types, and pointwise branch-permission joins. | First branching data programs while keeping interval dimensions separate from Boolean truth values. | No dependent motives, general data definitions, cubical rules, or preservation/canonicity theorem. Permission joining fixes the former exact-vector counterexample, not the whole metatheory. |
| [Unit rules](unit.md) | HOTT13 ch. 1 as ordinary-type background; explicit local prototype design | Add Unit : Type0 and () : Unit, both stable atoms under scope operations; constructor runtime usage is zero. Explicit UnitCase adds both children's usage and contracts on (). | First checked data value for ordinary source programs and reference evaluation. | No dependent eliminator, eta, general inductives, cubical behavior, or canonicity/preservation theorem; no implicit linear discard. |
| [Compatibility](../src/Fibril/Core/Compatibility.idr) | Staged universe design; CCHM18 integration still open | Compare literal universe levels directionally after normalization; otherwise require exact normal forms. | Allow ordinary checking at a larger universe without changing conversion. | Not a complete cumulative cubical calculus; no Pi covariance, symbolic levels, or preservation proof. |
| [WeakHead](../src/Fibril/Core/WeakHead.idr) | DEBRUIJN72 binding background | Contract head-spine beta and Unit/Boolean case redexes with explicit budgets. | Expose Pi/universe shape without normalizing irrelevant bodies; keep full conversion separate. | No general speed guarantee, confluence proof, or cubical head-reduction rules. |
| [Reduction](../src/Fibril/Core/Reduction.idr) | DEBRUIJN72; ATKEY18 as preservation background | Contract beta redexes using lifted substitution; compare normal forms with explicit fuel exhaustion. | Reference computation service for developing ordinary typed conversion without assuming arbitrary scoped terms terminate. | Fuel strategy is our choice; no eta/cubical conversion, normalization theorem, typed/quantitative preservation proof, or time bound. |
| [Context](../src/Fibril/Core/Context.idr) | ATKEY18 §2.1.3; DEBRUIJN72 | Store telescopes, shift dependent domains during lookup, and validate complete usage vectors. | Context infrastructure for future formation/inference judgments; preserves scope and identifies resource-policy failures by index. | Context storage alone does not check domains; erased checking does; the local permission policy is not a proved subusage calculus. |
| [Usage](../src/Fibril/Core/Usage.idr) | ATKEY18 §§2.1.1–2.1.3 | Represent mode-indexed variable use and combine/scale usage vectors; discharge the newest binder with a structured mismatch. | Accounting infrastructure for a future checker that distinguishes erased type information from runtime resource consumption. | Local helpers do not establish full context typing, subusage soundness, erased-vector invariants, or cubical resource rules. |
| [Term](../src/Fibril/Core/Term.idr) | DEBRUIJN72; ATKEY18 §2 | Encode variables by bounded nameless indices; represent quantity-annotated functions; lift renaming and substitution under binders to avoid capture. | Ordinary core syntax on which future elaboration, evaluation, and checking can agree. Scope indices prevent dangling variable references; substitution supports dependent result types and eventual beta computation. | No typing, conversion, or preservation theorem; our syntax is not a verbatim QTT presentation. |
| [Interval](../src/Fibril/Foundation/DeMorgan/Interval.idr) | CCHM18, interval algebra presentation | Represent dimension expressions with endpoints, reversal, meet/join, and structural substitution. | Geometric coordinate language for intended cubical paths and higher-dimensional constructions; lets future operations describe movement between endpoints without confusing dimensions with ordinary runtime Booleans. | Boolean vertex evaluation is not interval equality; path term checking is not implemented. |
| [Sorted](../src/Fibril/Foundation/DeMorgan/Sorted.idr) | Engineering optimization of CCHM18-inspired algebra services | Deduplicate sorted lists by adjacent scans and compare ascending clauses by merge walks. | Reduce canonicalization and subset-check overhead without changing solver algebra; frozen implementations provide differential tests. | Helpers assume lawful ordering/ascending inputs; no proof of solver correctness or removal of exponential growth. |
| [NormalForm](../src/Fibril/Foundation/DeMorgan/NormalForm.idr) | CCHM18, free De Morgan algebra | Push reversal to signed generators and compare absorbed disjunctive normal forms, preserving non-Boolean complement behavior. | Reference symbolic interval-equality service for future cubical checking; recognizes equivalent coordinate expressions without falsely identifying a dimension's boundary with the whole interval. | Our absorbed-DNF algorithm is an implementation choice, not code or a verified algorithm taken from the paper; worst-case growth is exponential. |
| [Face](../src/Fibril/Foundation/DeMorgan/Face.idr) | CCHM18, face lattice and restricted judgments | Represent endpoint constraints separately from intervals; normalize face formulas, decide entailment, extract endpoint faces, and substitute dimensions. | Boundary-logic service: express where a future cubical term must match a boundary and determine which constraints follow from others. Intended support for checking compatible boundary systems. | DNF solver correctness has tests, not a formal proof; boundary-system term checking is not implemented. |
| [Scope](../src/Fibril/Foundation/DeMorgan/Scope.idr) | DEBRUIJN72; CCHM18 dimension contexts | Bound dimension indices with Fin; validate raw expressions; provide scope-preserving weakening, substitution, and instantiation for intervals and faces. | Binding infrastructure for future dimension binders: reject out-of-scope coordinates and safely introduce or replace dimensions without capture or index confusion. | Scope indices alone establish neither typing nor resource safety. |
| [Restriction](../src/Fibril/Foundation/DeMorgan/Restriction.idr) | CCHM18, face-restricted contexts | Accumulate face assumptions, query entailment under them, detect empty restrictions, and reindex assumptions. | Local boundary-checking context: lets future checking reason on a particular face rather than require every boundary equation to hold on the entire cube. Empty faces make boundary obligations vacuous, not arbitrary global proofs valid. | Not a full cubical context or arbitrary theorem assumptions; no restricted term-equality checker exists. |
| [Proof examples](../examples/README.md) | HOTT13 ch. 1; Idris 2 implementation | Demonstrate indexed data, induction, equality proofs, and a structural substitution proof using ordinary functions. | Executable learning material and design feedback for Fibril's unified proofs/programs model; examples provide concrete scenarios to migrate to the future checker. | Executed/checked by Idris 2, not by Fibril; they do not establish Fibril's logical soundness. |

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
