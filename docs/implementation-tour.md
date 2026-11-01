# Implementation tour

Fibril is currently an Idris 2 bootstrap project with syntax/algebra infrastructure
and an **experimental erased ordinary checker**, not a complete Fibril language
checker or compiler.

![Implemented module dependencies](diagrams/modules.svg)

See [theoretical references and code correspondence](references.md) alongside
this tour. Each citation distinguishes implemented infrastructure from background
and future proof obligations.

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

## Usage accounting infrastructure

[Usage](../src/Fibril/Core/Usage.idr) adds erased/runtime modes, vectors of
coefficients, pointwise combination/scaling, and binder discharge errors.
The [core draft](core-draft.md#erased-and-runtime-relevant-judgments) describes
how a future checker should use these helpers. They do not yet traverse or type
terms, and local binder checks alone do not guarantee safe closure capture.

## Context infrastructure

[Context](../src/Fibril/Core/Context.idr) stores scoped telescopes, shifts dependent
types during lookup, and validates complete usage vectors. Its constructors do
not prove domains are types. The [checking plan](ordinary-checking.md) explains
how future inference differs from final context-permission validation.

## Reference computation

[Reduction](../src/Fibril/Core/Reduction.idr) performs bounded full beta reduction
and three-way normal-form comparison. [The reduction guide](reduction.md)
explains why exhaustion is inconclusive and why fuel is not a timing bound.
The [erased checker](erased-checker.md) now uses beta comparison for a small
ordinary fragment; an experimental ordinary runtime-usage layer now exists,
but cubical term checking remains absent.

## Randomized structural validation

[Hedgehog properties](../test/src/Tests/Properties.idr) now exercise substitution,
renaming, interval laws, and endpoint compatibility with bounded scope-correct
generators and shrinking. See [testing](testing.md) for dependency revisions,
replay instructions, and what these samples do not prove.
[Constructive erased typing properties](../test/src/Tests/TypedProperties.idr)
also test accepted term/type pairs, beta-step preservation, conversion, and
invalid expected types without filtering arbitrary syntax through the checker.

## Ordinary runtime usage

[Runtime](../src/Fibril/Core/Runtime.idr) layers usage inference over erased typing,
checks exact linear use and closure captures, and rejects runtime type expressions.
See [its guide](runtime-checker.md) for the conservative policy and unresolved
preservation/erasure obligations. No C or JavaScript runtime is implemented.

## Trust and current limits

The [experimental erased checker](../src/Fibril/Core/Erased.idr) validates
ordinary types and terms, including context formation, with explicit budgets.
Its success is not runtime resource permission or cubical proof validation.

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
