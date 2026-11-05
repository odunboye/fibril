# Inductive data: staged design and landing contract

**Status: D1, D2a closed identity and D2b checked declaration construction are
implemented. Non-recursive source declarations/constructors and optional named
elimination now work; direct source matching and D3/D4 remain proposals.**
The [finite-variant kernel](finite-variants.md) now implements the D1 primitive.
[Non-recursive source data](data.md) now supplies accepted declarations and named
elimination, not a positivity/source coverage/termination checker or soundness theorem. The remaining sections retain the landing
contract. [Closed nominal identity](nominal-data.md) now settles the non-recursive
kernel representation. [Checked declaration construction](data-declarations.md)
now allocates qualified keys and checks closed families/constructors, with exact
admission and all-or-error layout output. Source integration, field-telescope packing and ordinary module exports now work.
Direct source matching handles zero/unary non-recursive data. A restricted
[unary recursive declaration](data.md#unary-recursive-declarations) now lowers
to a finite, fixed-shape checked core type with a structural fold; it does not
introduce a general recursive declaration environment or positivity checker. A
separate built-in [Nat recursor](nat-recursion.md) and narrow single-argument
Nat equation form support structural computation, not a general termination
checker.

## Use cases

Records package fields that are all present. Alternatives express a choice:

- Optional A: a missing value or a present A, rather than a separate Bool whose
  relationship to a payload is left to the programmer.
- Result Error A: failure with an Error or success with an A, rather than a
  magic string or dummy success value.
- A finite protocol message: several distinct payload shapes, with a case for
  each accepted message.
- Later, List A and Nat: recursive collections/counts with structurally justified
  recursion and induction.

Prefer a record when all fields belong together, Bool for an uninformative
binary decision, or a direct value when there is no meaningful alternative.
Do not introduce Nat merely to get machine integers: this milestone is about
checked data and elimination, not an efficient numeric backend.

The first three uses need non-recursive alternatives. Lists/Nat additionally
need recursive declaration rules and positivity; ordinary recursive functions
need a termination story. These are distinct slices.

![Inductive-data landing stages](diagrams/inductive-data.svg)

## Why this is next

The existing core already has scoped dependent functions, quantity-aware
Box/Sigma, bounded conversion and independent erased/runtime checking.
Declaration lowering, direct-import publication and source services provide
places to integrate authored declarations without moving checking into a parser.

The missing capability is constructor choice with payloads and genuinely
dependent exhaustive elimination. Existing BoolCase has no dependent motive;
records have one packing. More dictionary/operator convenience does not close
this gap.

## Landing sequence and gates

| Stage | Deliverable | Must not claim |
| --- | --- | --- |
| D0: this design | Rules, representations, open decisions and acceptance tests. | Implemented data support. |
| D1: finite-variant kernel (implemented) | Non-recursive finite alternatives, including nullary arms, dependent elimination and reduction. | Recursive inductives, nominal data declarations or a preservation proof. |
| D2: authored non-recursive data | Declaration validation, a settled named-identity policy, checked constructors and exhaustive flat matching, module/editor integration. | Recursive self references, indices, nested coverage or termination checking. |
| D3: recursive declarations (partial) | Fixed terminal/unary-self recursive type and checked fold; general checked representation, positivity and List remain future work. | General recursion or arbitrary indexed/mutual datatypes. |
| D4: recursive function convenience | Structural recursion/termination checks and case-tree elaboration into admitted core terms. | Unrestricted recursion in types or proofs. |

Complete each slice with tests, use cases, diagrams, compatibility notes and a
commit. D1 does not silently authorize D2's public data syntax.

## D1: finite-variant representation (implemented)

Use an ordered, finite nonempty list of alternative descriptors:

~~~text
Arm(n) = Nullary | Payload(quantity, Term n)

VariantType : List Arm(n) -> Term n
VariantValue : Term n -> Nat -> Maybe (Term n) -> Term n
VariantCase : Term n -> Term n -> List (Term n) -> Term n
~~~

Arm(n) is notation; the current API uses Maybe (Quantity, Term n).
The three Variant constructors are now implemented; no runtime self-reference or recursive
signature environment is introduced. Raw syntax is not well-typed evidence:
constructor indices, arities, annotations and branches must all be checked.

There is **no fixed constructor-count maximum** in the language contract.
Source, nesting, declaration, generated-IR and expanded-core admission bound
work. A list representation must be counted before cloning and independently
post-counted, not repeatedly expanded to infer whether it fits.

Empty alternatives are deferred: empty elimination needs an explicit policy for
unreachable branches and ambient linear resources. One nullary alternative is
allowed; it does not acquire Unit conversion or eta.

D1 identity is structural for this internal primitive: ordered descriptors,
quantities and payload types determine conversion. Tags are positions, not
constructor spellings, source paths or nominal certificates.

### Formation and constructors

- Check every payload type in the erased judgement, including erased payloads.
- A nullary arm contributes universe level 0. The variant inhabits the maximum
  payload universe, with no Type : Type or implicit universe polymorphism.
- A constructor annotation T must expose a VariantType. Its tag must be in
  range. Nullary arms require no payload; payload arms require exactly one
  checked value at the declared type. Missing/extra payloads are errors.
- Runtime constructor usage is zero for a nullary arm, or q times the payload
  usage for Payload(q, A). Quantity 0 skips runtime traversal, not typechecking.
- The constructor tag remains computational data even when its payload is
  erased. Erasure of a field never erases the scrutinee's whole tag.
- Quantities are invariant under conversion, as for current Pi/Box/Sigma.

D1 payload domains are independent of a constructor field telescope. Multiple
fields can eventually be packaged with existing dependent Sigma/Box rules;
that lowering needs its own scope/admission tests in D2.

### Dependent elimination

For scrutinee s : T, require an explicitly checked erased motive:

~~~text
P : (0 self : T) -> Type j

branch_i : P (VariantValue T i Nothing)                   -- nullary
branch_i : (q x : A) -> P (VariantValue T i (Just x))      -- payload

VariantCase P s branches : P s
~~~

There must be exactly one branch per descriptor, in tag order. Even branches
not selected by a known constructor must be checked. The motive domain must
match T; its codomain must expose a universe. Use the existing explicit universe
and conversion-budget policies, not a guessed result level or new eta rule.

No Prop sort exists here. This proposal does not import a proof-irrelevance or
small-elimination restriction from another calculus.

Runtime checking adds scrutinee usage to the alternative-permission join of
branch usages. Payload branches are ordinary typed lambdas: their field
quantities are discharged exactly, and only ambient closure usage is joined.
Branches are alternatives, not sequential demands to be added together.

Consequences to test:

- An ambient linear value must be consumed appropriately in every possible arm.
- Payload quantity 1 forbids dropping/duplicating that payload.
- Using an ambient linear value twice within one branch still fails, even
  though only one arm is selected. An unrestricted constructor payload also
  cannot be populated from a linear ambient capture.
- Payload quantity 0 is usable in types/motives, not extracted as runtime data.
- A scrutinee and branch cannot both consume the same ambient linear input.
- An erased scrutinee cannot be inspected at runtime to discover its tag.

The last check must inspect the original term, preserving the existing global
stage barrier; normalization before usage analysis is not a workaround.

### Computation

~~~text
VariantCase P (VariantValue T i Nothing) branches -> branch_i
VariantCase P (VariantValue T i (Just value)) branches -> Apply branch_i value
~~~

Each selected elimination costs one contraction. Ordinary beta may follow.
Full and weak-head reduction must agree on these root rules and their fuel
accounting. Reduction must remain total on raw syntax: malformed tags/arity must
not crash a host list lookup. Such terms are rejected by checking; a raw reducer
can decline a malformed contraction.

No eta, no-confusion proof, constructor injectivity proof, equality reflection,
proof extraction or externally executed effect is introduced by these rules.

### Why not encode nullary constructors as Unit payloads?

With hidden Unit padding, a branch can produce P (Inject i ()) while the
eliminator needs P (Inject i u) for an arbitrary Unit variable u. Current Unit
has neither a dependent eliminator nor eta, so those types are not convertible.
The same issue motivated the genuine [unary wrapper](unary-records.md).

Explicit nullary descriptors avoid that mismatch without adding a conversion
principle, dropping a linear padding variable or weakening the motive.

## D2: authored declarations and matching

The following declaration syntax is now implemented (the fragment omits an
optional eliminator and main); see the runnable [data example](../examples/modules/data/Main.fib):

~~~fibril
data Optional (0 A : Type 0) : Type 0 where
  Nothing : Optional A
  Just : (1 value : A) -> Optional A
~~~

First validate a non-recursive declaration and its constructor telescopes.
Reject self/mutual references in payloads, arbitrary result targets, omitted
parameters, unsupported indices and forward dependencies. Resolve binding
identities, not substring matches of source names. Rejecting every recursive
occurrence at this stage is not a strict-positivity checker.

Publish a type only after its defining shape checks, then independently check
its constructor/eliminator definitions. Imported metadata is available only from
fully checked direct dependencies, as for current interface schemas. Metadata
is not a certificate that arbitrary constructor bodies can bypass checking.

Start with exhaustive flat constructor cases and explicit dependent motives;
constant-motive inference can be a separate convenience slice. Reject duplicate,
missing and foreign constructors. Avoid wildcard, nested-pattern and impossible-
case claims until their coverage/refinement rules exist. Authored branch names
must navigate to real constructor declarations; field binders remain lexical.

### Named data identity: closed D2a representation selected

Current records and D1's proposed finite variants are structural. Consequently,
two declarations with identical ordered shapes would be compatible if D2 merely
introduced transparent aliases. That is **not** nominal inductive type identity.

Before D2 lands, choose and document either:

1. Explicitly structural non-recursive data, with a deliberate compatibility and
   future migration policy; or
2. Nominal data references backed by independently checked declaration entries,
   with scoped parameters, stable module identity and rechecking semantics.

D2a now takes a closed nominal route: NominalType retains the exact key, all
parameter/index terms and full checked variant shape. This is not an opaque
name reference; keys alone confer no typing authority, mismatched shapes are
incompatible, and phantom parameters are not lost. See [the implemented contract](nominal-data.md).

D2b now supplies canonical key allocation and independent closed declaration/
constructor construction/checking. Source D2 now has authored grammar, field-telescope packing and ordinary checked
module exports. No constructor-layout schema is trusted/published for direct data
patterns yet; direct matching remains separate. Recursive data additionally needs a
representation/environment that does not infinitely unfold itself; D2a does not
provide it. Do not retrofit nominal record identity incidentally.

## D3/D4 boundaries

Nat/List need recursive declarations, not infinitely unfolded finite variants.
Specify constructor-result uniformity, strict positivity, universe formation,
recursor/induction hypotheses and their quantitative permissions before coding.
Negative recursion such as a constructor field D -> Bool must be rejected;
opaque aliases and higher-order occurrences must not evade validation.

General indices, mutual recursion, nested datatype positivity and large
elimination require explicit follow-up decisions. Equality/path types, cubical
transport, higher inductives and the quantitative/cubical combination remain
separate work; this plan inherits no metatheorem from their literature.

Recursive source functions may be added only with structural recursion or an
explicitly specified total alternative. Fuel in the host checker is not a
termination proof for a source-language recursive definition.

## Implementation inventory and acceptance gates

D1 updates the actual exhaustive consumers, not just a new checker clause.
See [the implementation evidence](finite-variants.md) for the completed checks.
The acceptance inventory is:

- [Core.Term](../src/Fibril/Core/Term.idr): raw constructors, scope operations,
  syntax comparison, and total list/descriptor traversal helpers.
- [Erased](../src/Fibril/Core/Erased.idr) and
  [Runtime](../src/Fibril/Core/Runtime.idr): all formation/arity/motive/usage rules.
- [Reduction](../src/Fibril/Core/Reduction.idr),
  [WeakHead](../src/Fibril/Core/WeakHead.idr) and pretty output: root contractions,
  total malformed-input behavior, deterministic fuel and explicit display.
- Renaming/substitution/composition/instantiation proofs and root-step facts:
  extend the existing host-checked structural statements without holes or axioms.
- Admission counters, raw and constructed typed generators, checked examples,
  reduction/rechecking properties, IO-inertness and regression tests.

The test matrix must include 1, 2, 3 and wider alternative lists; nullary and
payload arms; all three quantities; mixed universes; genuinely dependent motives;
both root rules; neutral scrutinees; invalid/extra/missing branches and payloads;
out-of-range tags; incompatible motives; branch joins and linear captures;
erased tags/payloads; malformed raw reduction; cumulative budget exhaustion;
and measured estimates covering every generated node.

D2 additionally requires source spans/diagnostics, source-order/import/privacy
checks, constructor navigation, formatting/shape guards, a runnable Optional/
Result use-case graph and tests rejecting unsupported recursion and coverage.

Run make test, make examples, make editor-test, make handbook and diff checks for
each implemented slice. Sampled reduction/rechecking tests are not subject
reduction proofs. Existing structural host proofs are not typed substitution,
canonicity, quantitative soundness, verified erasure or normalization proofs.
