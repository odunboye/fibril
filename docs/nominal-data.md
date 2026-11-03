# Closed nominal identity for non-recursive data

## Use cases

**Implemented internal kernel prerequisite D2a; no source data syntax yet.**
Use distinct identities when two data declarations have equal representations
but should not be interchangeable. OptionalEmail and OptionalUsername could both
contain either nothing or a String, yet mixing them should require an explicit
conversion. Such names alone do not validate email/username contents.

Retain all type/index arguments even when they are phantom: Flag String and
Flag Bool should not become compatible just because neither stores an element.
Prefer a transparent alias or existing structural record when interchangeability
is intentional. This slice does not change existing record identity.

The primitive is exercised in host Idris kernel tests. It is not an available
.fib declaration, a security boundary or a recursive datatype registry.

![Closed nominal identity](diagrams/nominal-data.svg)

## The chosen closed representation

[Core.Term](../src/Fibril/Core/Term.idr) now provides:

~~~idris
NominalType : String -> List (Term n) -> Term n -> Term n
NominalValue : Term n -> Term n -> Term n
NominalCase : Term n -> Term n -> Term n -> Term n
~~~

A type retains an exact key, its complete parameter/index vector, and its full
variant shape. Identity compares all three after existing bounded conversion.
Indices use ordinary definitional conversion; no extensional or proof-irrelevant
comparison is added. Keys are opaque exact strings, not reducible expressions.

This is self-contained nominal identity, not an opaque reference authorized by a
name lookup. The checker validates every index term in the erased judgement and
requires a fully well-formed shape exposing a nonempty VariantType. The resulting
universe is the shape's universe. Parameter kind/domain restrictions belong to
the future checked declaration family; the raw primitive accepts any well-typed
erased index. No unchecked declaration signature is imported by this operation.

Different keys distinguish equal shapes. Different phantom indices distinguish
otherwise equal instantiations. A key reused with another shape describes an
incompatible type, not permission to inhabit the original type. A constructor
value must still match the full annotated type's underlying shape. Raw syntax
and metadata are never typing certificates.

## Kernel example

This is host Idris, not source syntax:

~~~idris
optionalText : Term 0
optionalText = VariantType [Nothing, Just (Linear, StringType)]

email : Term 0
email = NominalType "Contact.OptionalEmail" [] optionalText

username : Term 0
username = NominalType "Contact.OptionalUsername" [] optionalText

someEmail : Term 0
someEmail = NominalValue email
  (VariantValue optionalText 1 (Just (StringValue "a@example.test")))
~~~

checkRuntime accepts someEmail at email and rejects it at username. An explicit
consuming unwrap/rewrap operation can convert compatible underlying payloads;
nominality is not a validation proof or an unforgeable runtime capability.

For a phantom family, NominalType "Example.Flag" [StringType] shape and the
same key with [BoolType] differ even if shape is a single nullary arm.

## Construction, dependent elimination and permissions

NominalValue T value checks T as a type, exposes its nominal shape, and checks
value against that exact shape. Runtime usage is the underlying value's demand;
keys, indices and type annotations do not create runtime demands.

For s : T with underlying variant V:

~~~text
P      : (0 self : T) -> Type j
branch : (1 value : V) -> P (NominalValue T value)
NominalCase P s branch : P s
~~~

The motive must have an erased matching domain and universe-valued codomain.
The branch consumes the variant once, then ordinary VariantCase can select its
constructor. Runtime checking adds scrutinee and branch closure demand, using
the original term. No runtime inspection of an erased wrapper is permitted.
Indices retained only in types do not discharge an ambient linear obligation.

~~~text
NominalCase P (NominalValue T value) branch -> Apply branch value
~~~

The contraction costs one step; beta and variant selection are separate. Full
and weak-head reduction agree on the root. There is no nominal eta, hidden Unit
or brand-field padding, quantity coercion or implicit cast. Reference wrappers
are not a guarantee about eventual backend layout.

## Declaration allocation is still a gate

Future source data lowering must allocate the same canonical qualified module/
declaration key for a declaration and carry all explicit parameters, including
phantom ones. It must reject duplicate/forward/recursive declarations as specified
for the first non-recursive source slice. The existing module graph establishes
checked direct-import/snapshot boundaries; it does not yet allocate these keys.

Only fully checked declarations may publish constructor layout metadata, and
constructor references must be validated against checked signatures and actual
packing. No arbitrary imported key or schema may authorize a constructor type.
A future family can enforce its parameter domains with ordinary typed erased
lambdas; raw-core construction of a different indexed type is not evidence of
membership in that source family.

This decision settles a closed non-recursive representation, **not** a recursive
declaration environment. Recursively embedding a shape would infinitely unfold
it. Nat/List still require a separately checked environment/reference/recursor
contract, strict positivity and quantitative induction rules. This slice adds
no such references, registry, source coverage or termination checker.

## Bounds and evidence

Core/module counters charge index-list cells and all shape/value/branch terms.
Saturated inference counters and partial scope transport retain phantom index
dependencies. Index validation is depth-bounded; existing type-reduction fuel
applies. No allocation, timing or whole-language soundness theorem is claimed.

Renaming/substitution/fusion/composition proofs include all three constructors
and index lists. Derived instantiation facts remain total; the actual nominal
root contraction has checked scope-transport equations. These remain structural
host proofs, not typed substitution or subject reduction.

[Tests.Nominal](../test/src/Tests/Nominal.idr) covers key/phantom/layout distinctions,
malformed shapes and indices, beta-equivalent indices, erased/linear index use,
consuming and genuinely dependent elimination, reduction/rechecking, scope
transport and admission/depth counts. Raw and constructed erased/runtime
property generators include nominal wrappers without checker-based filtering.

Next: authored non-recursive declarations, checked key allocation and constructor
metadata, then exhaustive flat source matching. See the [staged plan](inductive-data.md).
