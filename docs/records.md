# Dependent records: kernel foundations

**Status:** core dependent pairs and a bounded named-record source prototype are
implemented. Source records currently have exactly two fields, an explicit
constructor and an explicit eliminator. Parameters, recursive/nominal records,
pattern syntax, projections, field-name resolution and interface dictionaries
remain unimplemented. No preservation or erasure theorem is claimed.

Records will elaborate into genuinely dependent structure, not a temporary
nondependent product. [Erased named globals](interfaces.md#first-prerequisite-erased-global-type-declarations-implemented)
already provide the module-level type declaration boundary.

## Named source records

[The runnable example](../examples/modules/records/Main.fib) prints Records!:

~~~sh
./build/exec/fibril run --source-dir examples/modules/records examples/modules/records/Main.fib
~~~

It combines a genuine dependent package with a consuming message record:

~~~fibril
export
record Package : Type 1 where
  constructor MkPackage
  eliminator unpackPackage
  0 Item : Type 0
  1 value : Item
~~~

The field value has the type supplied in Item. For example, MkPackage String
"payload" checks, while MkPackage Bool "payload" rejects. The type is erased;
the payload is linear. This is not a parser shortcut for a particular record.

The current grammar requires a named module, a column-one record header, then
aligned indented constructor/eliminator directives and exactly two single-line
typed fields. Comments/blank lines are allowed. No parameters, defaults,
recursive references, multiline field expressions, inferred field types or
automatic accessors are added. Field names must be distinct and referenceable.
Quantities are 0, 1 or unrestricted (the existing omitted-quantity default).
record, constructor, eliminator and where are now reserved lowercase keywords.

Source ordering is meaningful: the first type sees the outer environment; the
second type additionally sees the first field. It cannot refer to itself or a
later field. Generated internal binders cannot be captured by legal source names;
even fields named Package or MkPackage do not capture generated global references.

A record expands to three ordinary checked declarations: an erased type, an
unrestricted constructor, and an unrestricted consuming eliminator. These count
as **three** of the existing 64 declaration slots. All three go through existing
resolution, pre-clone size admission, and erased/runtime checking; expansion is
not an axiom or permission to skip generated bodies. The explicit eliminator
directive gives it a real source name/location, rather than inventing a
definition location for an auto-named function.

export applies to the whole group. Without it all three names remain private.
Partial/opaque record export is not implemented. A failed generated definition
prevents publishing the enclosing module interface.

### Calling the eliminator

For a record R : Type l with fields q x : A and r y : B x, a declaration
eliminator consumeR generates this schematic signature:

~~~text
consumeR :
  (0 P : (0 self : R) -> Type l) ->
  (1 value : R) ->
  (1 branch : (q x : A) -> (r y : B x) -> P (MkR x y)) ->
  P value
~~~

The result universe is the **declared** record universe, not inferred
polymorphism. Pi conversion is invariant. To use a small result with a Type 1
record, give an explicit upward type ascription inside the motive, for example
\(0 self : R) => (String : Type 1). This does not add covariance.

The Package example defines a checked erased payloadType using unpackPackage
at Type 1, then a runtime recover whose return type is payloadType package.
Its branch returns the linear payload, and its motive computes the correct
type. This demonstrates dependent elimination from source, not just a constant
result or a precomputed output.

For a Type 0 message record with two linear fields:

~~~fibril
record Message : Type 0 where
  constructor MkMessage
  eliminator consumeMessage
  1 loud : Bool
  1 text : String
~~~

A consuming call can be:

~~~fibril
consumeMessage (\(0 self : Message) => String) message
  (\(1 loud : Bool) => \(1 text : String) =>
    if loud then appendString text "!" else text)
~~~

Both fields are used according to their quantities. A branch that drops loud,
duplicates text, changes the binder quantities, or extracts an erased field at
runtime is rejected. There is no special syntax for patterns yet: callers pass
an ordinary explicitly typed branch function.

### Structural, not nominal

This first lowering produces transparent Sigma abbreviations. Two named
records with the same normalized field types/quantities are definitionally
compatible even if names differ. **No generative nominal identity or record eta
rule is implemented.** The tests record this policy explicitly; do not assume
the full Idris record model or an opaque abstraction boundary.

Nominality, richer export policy and parameters need separate design before
claiming general-purpose interface record identity. Changing those rules will
require rechecking affected programs, not a metadata-only change.

### Source tooling

Symbols expose the three actual name tokens. Definition queries link constructor
and eliminator calls to their real directive names, and record types to their
header. Generated expression bodies have no separate authored source spans, so
navigation deliberately does not walk their synthetic copies. Field-level
references/rename/navigation inside the declaration are not implemented rather
than duplicated or attached to guessed locations. Existing module rename
previews remain blocked. Core failures remain unlocated.

## Two-field core representation

The remaining examples in this section use Idris host constructors, not raw
Fibril Sigma/PairCase syntax.

[Core.Term](../src/Fibril/Core/Term.idr) now provides:

~~~idris
Sigma : Quantity -> Quantity -> Term n -> Term (S n) -> Term n
PairValue : Term n -> Term n -> Term n -> Term n
PairCase : Term n -> Term n -> Term n -> Term n
~~~

Sigma q r A B binds the first field in B. The first field has quantity q and
the second quantity r. B cannot refer to the second field itself. No value
member projection is implied by qualified source dots.

PairValue sigma first second retains an explicit type annotation. The checker
validates its formation, exposes its Sigma head with bounded reduction, checks
first against A, then second against B[first/x]. It does not infer a dependency
family from a pair of values or accept an annotation as an axiom.

Examples constructed in [Tests.Sigma](../test/src/Tests/Sigma.idr):

~~~idris
-- The second field's type depends on the actual first field.
family = Sigma Linear Linear BoolType
               (BoolCase (Variable FZ) StringType BoolType)

-- Accepted: True selects String, False selects Bool.
PairValue family BoolTrue (StringValue "yes")
PairValue family BoolFalse BoolTrue

-- Rejected: False selects Bool, not String.
PairValue family BoolFalse (StringValue "wrong")
~~~

A second example packages a small type with a value of that type:

~~~idris
packageType = Sigma Erased Linear (Universe 0) (Variable FZ)
PairValue packageType StringType (StringValue "payload")
~~~

The first field is checked but not demanded as runtime type data. Its quantity
must make that distinction explicit. This package has type-level universe 1,
not universe 0: its first field ranges over Type 0.

## Formation and conversion

If A has sort Type i and B has sort Type j in the context extended by x : A,
Sigma q r A B has sort Type (max i j). The erased checker validates both field
types; quantities are usage permissions, not substitutes for formation checks.

Conversion compares normalized structure, including **both** quantities. There
is no Sigma covariance, quantity coercion, record eta rule, proof irrelevance,
or equality/path witness added by this slice. Literal universe compatibility
remains the existing separate rule.

A type annotation may compute to a Sigma, but exhausted exposure/conversion
remains explicit failure. A well-formed annotation with the wrong outer shape
reports ExpectedPairType. Rich payloads remain unlocated core data, not invented
source spans.

## Runtime usage for introduction

After erased typing succeeds, pair introduction contributes:

~~~text
q * usage(first) + r * usage(second)
~~~

Annotations are erased. A quantity-0 field is still typechecked, but its value is
not analyzed as a runtime expression. Nonzero fields use the ordinary runtime
analysis; all combined ambient permissions are validated as before.

Consequences exercised by tests:

- A runtime-demanded type field is not allowed merely because it is inside a pair.
- Two linear fields containing the same linear ambient variable are rejected.
- An unrestricted field scales a captured linear variable to unrestricted use
  and is rejected, rather than becoming a copying loophole.
- An erased field adds no runtime capture usage, but an ill-typed erased field
  still rejects construction.
- Sigma types themselves remain unsupported runtime type expressions.

This extends the prototype usage analysis; it is not a proof of quantitative
subject reduction or safe backend representation/erasure.

## Computation, scope, and evidence

Full normalization traverses Sigma domain/body and pair annotation/first/second
in source-constructor order. Weak-head inspection treats Sigma and PairValue as
exposed heads, without inspecting their fields. PairCase has the root rule described below.

Renaming/substitution lift once under the Sigma's first-field binder. Pair
components all live in the ambient scope. Host renaming identity/composition,
substitution congruence/composition/interchange, and the existing derived
instantiation/root-beta/fuel lemmas cover the extended term language. These are
structural facts, not a typing metatheory.

Raw scoped generators now include both constructors. Erased typed recipes include
an existential type/value package and pair wrappers. Runtime recipes wrap a
captured linear value with an erased Unit field and a linear second field.
Sampled preservation/rechecking properties cover these recipes; they are not
universal preservation proofs. Pretty printing and module node accounting also
include both constructors. Per-file/graph/checking/reduction limits are unchanged.

## Consuming dependent elimination

PairCase motive scrutinee branch stores three ordinary terms, not a new
two-binder AST node. Its motive has an erased input and a universe result:

~~~text
motive : (0 p : Sigma q r A B) -> Type l
branch : (q x : A) -> (r y : B x) -> motive (pair x y)
PairCase motive scrutinee branch : motive scrutinee
~~~

Here pair x y denotes PairValue with the validated scrutinee type annotation;
these are schematic rules, not source syntax. Domains, the universe-valued
motive, dependent branch result, and both quantities are checked. A merely
function-shaped motive is insufficient. Universe/capture failures remain
bounded checking failures, not trusted metadata.

Runtime analysis counts the scrutinee once plus the branch function once.
Ordinary lambda checking enforces both field permissions. The motive and
annotations are erased. Dropping/duplicating a linear field, extracting an
erased field as runtime data, or using a linear ambient capture in both the
scrutinee and branch fails. An erased ambient record is not runtime input.

The root rule is:

~~~text
PairCase motive (PairValue sigma first second) branch
  --> (branch first) second
~~~

The following two beta steps use existing capture-safe lambda substitution.
There is no ad hoc two-index substitution or new scope-lifting convention.
Branch functions and motives contain ordinary binders when needed. Full
normalization traverses motive/scrutinee/branch when no root rule applies;
head evaluation forces only the scrutinee until a constructor is exposed.

Tests include a genuinely dependent payload-type motive: it computes the first
(erased type) field of an existential package during typechecking, and its
runtime branch returns the second field. This type-level computation is not a
runtime projection of erased data. Evaluation consumes three root/application
steps and its result is checked again against String. Additional cases cover
motive/domain/result failures, exact branch quantities, fuel exhaustion,
ambient captures, and normal-form rechecking.

All structural host proofs now include PairCase. Known root pair-case
contractions commute with renaming/substitution by checked host equalities;
subsequent beta naturality reuses the existing laws. Generators include raw
cases and typed/runtime case recipes. This still is not a general preservation
or quantitative soundness theorem.

## Remaining record work

The constructor/eliminator core and the bounded two-field source declarations
are in place. Next work includes record parameters, broader field counts,
consuming pattern syntax, nominality decisions, and richer visibility. Do not implement fst/snd by
silently discarding a linear component. Multiple fields need an explicit
nesting/tail policy and generated eliminators must preserve the same permissions.
Interfaces can then lower into those checked values. No automatic projection, record eta, or dictionary inference is claimed yet.
