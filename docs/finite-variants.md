# Finite variants: internal checked kernel

## Use cases

**Implemented kernel slice D1; no source data syntax yet.** This gives compiler
work on Optional/Result and finite messages a checked representation of actual
constructor alternatives, rather than unrelated Bool/payload values. Nullary
arms represent absence/tags; payload arms represent a selected value with an
explicit permission. A genuinely dependent case can compute its result type
from the tag or an erased carried type.

This API is currently exercised through Idris kernel tests, not by writing data
in a .fib file. Prefer existing records for packaging fields all present, Bool
for a plain decision, and direct values when no alternative is needed. Recursive
Nat/List, named nominal data and general source coverage are not implemented.

![Finite-variant checking and reduction](diagrams/finite-variants.svg)

## Representation and a concrete kernel example

[Core.Term](../src/Fibril/Core/Term.idr) exposes:

~~~idris
VariantType : List (Maybe (Quantity, Term n)) -> Term n
VariantValue : Term n -> Nat -> Maybe (Term n) -> Term n
VariantCase : Term n -> Term n -> List (Term n) -> Term n
~~~

Nothing in the type's descriptor list is a nullary arm; Just (q, A) is one
payload of type A with quantity q. Constructor tags are zero-based positions.
A value has an explicit type annotation, tag, and Nothing/Just payload.
A case has an erased dependent motive, scrutinee and positional branches.
These are raw syntax constructors, not typing certificates.

For an optional String, a test can construct the following **host Idris** terms:

~~~idris
optionalString : Term 0
optionalString = VariantType [Nothing, Just (Linear, StringType)]

present : Term 0
present = VariantValue optionalString 1 (Just (StringValue "present"))

result : Term 0
result = VariantCase (Lambda Erased optionalString StringType) present
  [StringValue "missing", Lambda Linear StringType (Variable FZ)]
~~~

checkRuntime 512 128 Empty result StringType accepts this term; normalize 2
reduces it to StringValue "present". The nullary constructor instead selects
"missing" in one contraction. This is a kernel example, not new surface syntax.

## Implemented checking rules

- Descriptors must be nonempty. Empty-type elimination is deferred.
- Each payload domain is checked as a type, even when its quantity is erased.
  The result universe is the maximum domain universe; nullary arms contribute 0.
- A value's annotation must expose a variant type. Its tag must be in range,
  with precisely the payload arity and type required by that descriptor.
- The motive must have an erased matching variant domain and a universe-valued
  codomain. For scrutinee s and motive P, the result is P s.
- A nullary branch checks at P (Inject T tag Nothing). A payload branch checks
  at (q value : A) -> P (Inject T tag (Just value)).
- There must be exactly one branch per arm. Every branch is checked, even for a
  statically visible constructor. Payload quantities remain conversion-invariant.

Identity is structural and ordered. It is not nominal identity, and two nullary
arms do not make this type convertible to the existing Bool. Nullary arms do
not contain hidden Unit padding or acquire Unit eta.

## Runtime permissions and computation

Nullary construction has zero usage. Payload construction scales demand by its
quantity; erased payloads are fully typechecked but skipped by runtime analysis.
The tag itself remains runtime-relevant.

A case adds scrutinee demand to the permission join of its branches. Branch
lambdas discharge payload permissions normally; their ambient closure demands
are joined, not sequentially added. A one-branch join is that branch, not a join
with zero. Linear captures must still be used correctly in every alternative.
Erased scrutinee tags and erased payloads cannot be extracted at runtime.

~~~text
VariantCase P (VariantValue T i Nothing) branches -> branch_i
VariantCase P (VariantValue T i (Just value)) branches -> Apply branch_i value
~~~

The selection costs one contraction; ordinary beta is separate. Both full and
head reduction use the same total selection function. Out-of-range raw tags do
not crash. Raw reduction is not a type/arity validator; it can reduce ill-typed
syntax, just as ordinary beta can. Drivers check original terms before reduction.
There is no eta, no-confusion/injectivity theorem, recursive self reference or
effect execution in the reducer.

## Bounds and structural evidence

There is no fixed alternative-count cap. Checker depth bounds descriptor and
branch traversal. Module clone accounting and saturated elaboration size
estimation count every descriptor/branch cell as well as payload subterms;
empty lists do not make long nullary shapes free. Existing admission limits still
apply. Fuel counts contractions, not time or allocation.

Scope operations, syntax comparison, display, partial scope transport and
counters include all descriptors/payloads/branches. Renaming, substitution,
fusion/composition and derived instantiation facts remain host-checked and total.
[Root laws](../src/Fibril/Core/Reduction/Beta.idr) cover shared selection at every
tag and actual reducer equations for known selected nullary/payload roots.
These are structural statements, not typed substitution or subject reduction.

[Tests.Variant](../test/src/Tests/Variant.idr) exercises dependent type recovery,
universes, all quantities, branch joins, invalid tags/arity/motives/branches,
neutral and malformed raw terms, fuel, 1/2/3/9/16 arms, scope transport, size/depth
limits and inert erased IO payloads. Raw scoped and constructed erased/runtime
generators now include variants; sampled reduction/rechecking tests remain tests,
not canonicity, soundness, normalization or verified erasure proofs.

[Closed nominal wrappers](nominal-data.md) now add non-recursive identity without
changing the structural variant primitive. Next: [D2 source declaration checking](inductive-data.md). No source
parser keywords, instance registration, recursive data, positivity checker,
termination checker or cubical computation are added by D1.
