# Implementation tour

Fibril is currently an Idris 2 bootstrap project. It has useful syntax and
algebra infrastructure, **not a working Fibril language checker or compiler**.

![Implemented module dependencies](diagrams/modules.svg)

## Read the implementation in this order

1. [**Quantity**](../src/Fibril/Core/Quantity.idr) defines 0, 1, and unrestricted coefficients, arithmetic, and a
   proposed local binder policy. It does not enforce program usage.
2. [**Interval**](../src/Fibril/Foundation/DeMorgan/Interval.idr) defines De Morgan syntax, structural substitution, and evaluation
   at Boolean vertices. Vertex agreement is not symbolic equality.
3. [**NormalForm**](../src/Fibril/Foundation/DeMorgan/NormalForm.idr) compares free De Morgan expressions using absorbed DNF.
   Complementary literals are not cancelled. Worst-case growth is exponential.
4. [**Face**](../src/Fibril/Foundation/DeMorgan/Face.idr) supplies a separate lattice: opposite endpoints are disjoint, but
   not exhaustive. It implements entailment, endpoint extraction, and substitution.
5. [**Scope**](../src/Fibril/Foundation/DeMorgan/Scope.idr) bounds dimensions with Fin indices and supplies safe structural
   operations and raw-syntax validation.
6. [**Restriction**](../src/Fibril/Foundation/DeMorgan/Restriction.idr) accumulates face assumptions and checks obligations under them.
   An empty face is legitimate, not an arbitrary proof of false.
7. [**Term**](../src/Fibril/Core/Term.idr) provides scoped ordinary dependent-function syntax, renaming,
   substitution, and syntactic equality. Scoped does not mean well typed.

Browse annotated files through the handbook's **Source index** link. Public APIs
are also available in the generated API reference.

## Calls across the implementation

![Selected function calls](diagrams/calls.svg)

This is a **curated static call graph**, not a runtime profile or exhaustive
compiler-generated graph. It omits self-recursive edges, standard-library
functions, constructors, and some helper calls for readability. The source of
truth is the linked code. Update the graph when these relationships change.

Notable flows:

- Restriction holds -> scoped entailment -> raw face entailment -> face DNF.
- Scoped substitution extracts endpoint faces instead of treating faces as Bool.
- Term substitution lifts replacements under binders using weakening/renaming.
- Symbolic interval equality and face equality use distinct normal forms.

## Trust and current limits

All these modules are implemented in Idris 2. Tests cover examples and finite
corpora; they do not establish metatheory. No quantitative cubical soundness,
normalization theorem, verified compiler, or real-time guarantee exists yet.

![Intended compiler architecture](diagrams/roadmap.svg)

Dashed roadmap nodes represent unimplemented compiler stages. C and JavaScript
are intended targets, not existing backends.

## Milestones completed

- Bootstrap CLI, pinned pack configuration, and separate test package.
- De Morgan interval equality, face entailment, endpoint extraction/substitution.
- Scope-indexed dimensions and restriction contexts.
- Quantity algebra and scope-indexed ordinary terms.
- Runnable Idris bootstrap examples, checked Idris proofs, and labeled proposals.
- Documentation policy, generated API pages, and contributor checklist.
- Pipelines dependency evaluation; adoption deferred, no dependency added.

For exact revisions, use `git log --oneline`. See the design record for decisions
and open questions, not just the implemented subset.
