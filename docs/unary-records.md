# Singleton records and the unary kernel

**Implemented prototype:** one-field records lower to a quantity-aware unary
wrapper, not to the naked field type or a pair with hidden Unit padding.
This extends the checked term language; it does not establish preservation,
quantitative soundness, verified erasure, or computational HoTT.

![Unary record lowering and checking](diagrams/unary-records.svg)

## Why a real unary wrapper?

Unit currently has no dependent eliminator or eta rule. For padded pairs,
a branch returning P (pair value ()) cannot generally satisfy
P (pair value padding). Replacing padding with () in the checker would silently
add a conversion principle. A unary wrapper needs no padding or such principle.

## Implemented core checks

The internal constructors in [Core.Term](../src/Fibril/Core/Term.idr) are:

~~~text
BoxType : Quantity -> Term n -> Term n
BoxValue : Term n -> Term n -> Term n
BoxCase : Term n -> Term n -> Term n -> Term n
~~~

BoxType q A inhabits the same universe as A. BoxValue T value requires T
to expose a BoxType q A and value to inhabit A. The annotation and payload are
fully typechecked, even when q is erased.

For scrutinee : BoxType q A, elimination checks:

~~~text
P      : (0 self : BoxType q A) -> Type level
branch : (q x : A) -> P (BoxValue (BoxType q A) x)
result : P scrutinee
~~~

These are implemented prototype rules, not a metatheoretic derivation.
The branch quantity must match exactly; Pi conversion does not coerce it.
A motive must have an erased matching domain and universe-valued result.
See [erased checking](../src/Fibril/Core/Erased.idr) and
[runtime analysis](../src/Fibril/Core/Runtime.idr).

Runtime construction scales payload demand by q and skips runtime traversal of
an erased payload. Elimination adds scrutinee and branch demands, invoking the
branch once; its ordinary lambda check discharges the field:

- A linear field cannot be discarded or duplicated.
- An unrestricted field can be discarded or reused, but cannot be constructed
  from a linear ambient capture under unrestricted demand.
- An erased field remains available in types/motives, not as extracted runtime
  data. Erased embedded IO descriptions do not execute.
- A linear scrutinee and branch cannot both capture the same linear input.

The computational rule is:

~~~text
BoxCase P (BoxValue T value) branch -> Apply branch value
~~~

This costs one contraction, followed by ordinary beta if applicable. Full and
weak-head reduction implement it. No box eta, projection shortcut, implicit
quantity coercion, or nominal identity is added. Box is an internal term tag,
not a source primitive keyword or a promise of heap allocation/native layout.

## Source lowering

~~~fibril
record Combine (0 A : Type 0) : Type 0 where
  constructor MkCombine
  eliminator useCombine
  combine : (left : A) -> (right : A) -> A
  projection operation combine
~~~

The parser retains one authored field. The declaration elaborator emits an
erased type abbreviation, constructor and consuming dependent eliminator, plus
the requested getter. Each definition passes ordinary resolution, construction
admission and erased/runtime checking. The generated eliminator retains the
existing declared result-universe policy.

The getter consumes the wrapper once; it is rejected for an erased field.
Field counts still have no fixed maximum; generated-IR, source, declaration and
checker budgets apply. Empty records remain rejected. Binary records retain
their existing Sigma representation, and wider records retain linear nested
tails. Typed source case patterns now support one unary binder, with an explicit
return or [bounded motive inference](pattern-inference.md).

Identity remains structural: two singleton records with equal normalized field
types/quantities are compatible, but neither is its naked payload type or a
padded pair. Changing nominal identity remains separate work.

[The operations example](../examples/modules/singleton-records/Main.fib)
prints Singleton records! using an explicit quantity adapter. It is not an
interface declaration or a proof of associativity.
[The dependent example](../examples/modules/singleton-records/Dependent.fib)
constructs an identity function at an erased wrapped type and prints
Dependent singleton!; its motive genuinely depends on the record.

## Evidence and limits

[Tests.Box](../test/src/Tests/Box.idr) exercises formation, dependent motives,
reduction/fuel and result rechecking, quantity invariance, erasure, linear
capture/discard/duplication and malformed annotations/motives.
CLI tests cover source lowering, checked execution, module dictionaries,
structural compatibility, unsafe getters, erased effects and normal formatting.
Construction preflight counts unary nodes; the generated size is independently
checked against its estimate.

Raw scoped and constructed erased/runtime generators include unary terms.
Host renaming, substitution, composition, instantiation and root-step
compatibility facts include these constructors; root elimination equations are
checked in [Reduction.Beta](../src/Fibril/Core/Reduction/Beta.idr).
These prove structural syntax facts, not typed substitution or subject reduction.
Generated reduction/rechecking properties are sampled tests, not proofs.
