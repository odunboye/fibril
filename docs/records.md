# Dependent records: kernel foundations

**Status:** core dependent pairs and a bounded named-record source prototype are
implemented, including explicitly requested safe projection functions. Source records have no fixed field-count cap (at least one field), an explicit
constructor and an optional named eliminator. Explicit erased parameter telescopes are supported; recursive/nominal records,
constructor-discriminating/inferred patterns, dot-field syntax and instance
inference remain unimplemented. [Explicit interfaces](explicit-interfaces.md)
now reuse these checked dictionary foundations. No preservation or erasure theorem is claimed.

Records will elaborate into genuinely dependent structure, not a temporary
nondependent product. [Erased named globals](interfaces.md#first-prerequisite-erased-global-type-declarations-implemented)
already provide the module-level type declaration boundary.

[Parsing and declaration elaboration](elaboration.md) are now separate. The parser
retains authored records; a dedicated elaborator generates definitions and checks
projection/parameter policy. Syntax-only tools do not expand bodies. Use
elaborate PATH to inspect the resulting unchecked named IR.

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
an aligned indented constructor directive, an optional eliminator directive, and at least one single-line
typed fields. Comments/blank lines are allowed. No defaults,
recursive references, multiline field expressions, inferred field types or
automatically inferred accessors are added. Optional projection directives follow
the fields, as described below. Field names must be distinct and referenceable.
Quantities are 0, 1 or unrestricted (the existing omitted-quantity default).
record, constructor, eliminator and where are now reserved lowercase keywords.

Source ordering is meaningful: each field type additionally sees all earlier
fields, forming a genuinely dependent telescope. It cannot refer to itself or a
later field. Generated internal binders cannot be captured by legal source names;
even fields named Package or MkPackage do not capture generated global references.

A record expands to an erased type and unrestricted constructor, plus an
unrestricted consuming eliminator **only when its directive is present**.
These consume **two or three** of the existing 64 declaration slots, respectively.
Every generated declaration goes through existing
resolution, pre-clone size admission, and erased/runtime checking; expansion is
not an axiom or permission to skip generated bodies. An explicitly requested eliminator
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
runtime is rejected. The pattern form below is equivalent core elimination.

### Explicit consuming patterns

Two-field consuming patterns are now accepted:

~~~fibril
case message return (\(0 self : Message) => String) of
  (1 loud : Bool) (1 text : String) =>
    if loud then appendString text "!" else text
~~~

The return clause is an explicit **motive**: a type-level function of the whole
scrutinee. It is not an IO return operation. return is now reserved syntax.
The two parenthesized binders provide quantities, names and types; the second
type sees the first binder. The body sees both. Non-wildcard names must be
distinct. The scrutinee and motive are resolved in the outer environment, never
under pattern binders.

This lowers directly to PairCase with a curried branch function, not to text
substitution, record-specific host execution, or unchecked generated getters.
Core checking verifies the scrutinee is a Sigma, the motive returns a type, and
branch quantities/types match exactly. Fields may be named differently from
their declaration: this is structural, not constructor-discriminating matching.

An underscore is a typed wildcard, not permission to discard anything. An erased
or unrestricted field can be ignored when its permission allows it. A wildcard
on a linear field still fails if that field is not consumed. Erased fields do
not become runtime data through a pattern.

The [Patterns example](../examples/modules/records/Patterns.fib) computes a
dependent payload type using an erased case, recovers the linear payload with
a dependent motive, then consumes a message and prints Patterns! The
[parameterized Indexed example](../examples/modules/record-parameters/Data/Indexed.fib)
also rebuilds a value using this syntax.

Pattern motives use the core's universe-valued motive rule, rather than being
limited to the named generated eliminator's fixed result universe. [Bounded motive inference](pattern-inference.md) now permits omission for
independent results and canonical dependent results built from erased field
extractions. Explicit return remains available, including after inference-budget
exhaustion. Binder types remain authored; multi-branch coverage,
constructor-pattern grammar and boolean/inductive refinement remain absent.

The old case value of () => body syntax is unchanged. A typed record case
has one unary or two pair binders and one body, with an optional return clause. General expression layout works
inside declarations; the existing flat physical-line do-statement restriction
has not been lifted.

Definition/reference/lexical rename traversal uses the actual pattern binder
tokens and domains. Generated record bodies still have no invented authored
locations. Project-wide rename remains unsupported.

### Safe projection functions

Request getters explicitly after the field declarations:

~~~fibril
export
record Package : Type 1 where
  constructor MkPackage
  eliminator unpackPackage
  0 Item : Type 0
  1 value : Item
  projection getValue value
~~~

getValue consumes one Package and returns a value of its packaged Item type.
The return type genuinely depends on the argument. No runtime getter for Item
is generated: it is an erased field.

For reusable dictionaries, both fields may permit discarding:

~~~fibril
record Dictionary (0 A : Type 0) : Type 0 where
  constructor MkDictionary
  eliminator useDictionary
  combine : (left : A) -> (right : A) -> A
  identity : A
  projection getCombine combine
  projection getIdentity identity
~~~

Invoke these as ordinary functions with explicit parameters, for example
getCombine String dictionary left right. projection is now reserved syntax.
There is **no .field syntax** or automatic name/field inference.

The grammar permits aligned projection getter field lines after the fields,
without a fixed per-record request cap. Targets must be declared field names; getter names must be
referenceable and distinct from existing declarations. Each request generates
one unrestricted function, taking the record with quantity 1 after its erased
parameters. It shares the record group's export policy and consumes one
declaration slot. Its symbol/definition points to the actual getter name token.

Generation requires both:

1. The selected field permits one runtime use (quantity 1 or unrestricted).
2. Every discarded field permits zero uses (quantity 0 or unrestricted).

A request selecting an erased field or dropping a linear one is rejected, not
silently omitted and not granted a weaker quantity. The generated function is
then resolved, typechecked and resource-checked normally. This policy check is
not an unchecked core projection rule.

Two calls on the same quantity-1 record still use that record twice and reject.
A reusable record binder can permit repeated calls; calling a getter does not
make a linear record reusable. For two linear fields, use a consuming pattern;
for wider records, use the generated eliminator rather than an unsafe getter.

A getter's result type substitutes erased extractions of the earlier fields it
depends on, including transitive type dependencies. Unneeded predecessors are not
expanded. Type-level extraction follows only the required nested-pair path. That extraction lives only
inside types and motives, using erased checking. It is not a public/runtime
getter for erased data. The runtime branch returns the selected field and must
obey the original quantities. This is why a Package payload getter works
without reviving its erased type field or discarding a linear runtime field.

The [projection example](../examples/modules/record-projections/Main.fib) combines
a dependent payload getter and parameterized operation/identity getters and prints
Safe projections! Tests cover both positions across all quantity combinations,
dependent Bool-indexed and type-indexed results, private/parameterized module
behavior, source targets, declaration budgets, and linear double-use rejection.

Getter generation itself adds no conversion rule, borrowing/lens semantics,
or metatheoretic certificate. Singleton records use the explicit unary kernel
constructors described separately. Optional functions are still transparent checked
lowerings into PairCase; nominality and richer visibility remain separate work.

### Structural, not nominal

This first lowering produces transparent Sigma abbreviations. Two named
records with the same normalized field types/quantities are definitionally
compatible even if names differ. **No generative nominal identity or record eta
rule is implemented.** The tests record this policy explicitly; do not assume
the full Idris record model or an opaque abstraction boundary.

Nominality, richer export policy and inferred arguments need separate design before
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

## Record parameters

Record headers accept up to eight explicit erased binders on the same physical
header line. For example, a reusable operational dictionary is ordinary source:

~~~fibril
record AppendDictionary (0 A : Type 0) : Type 0 where
  constructor MkAppendDictionary
  eliminator useAppendDictionary
  combine : (left : A) -> (right : A) -> A
  identity : A
~~~

The [parameterized record example](../examples/modules/record-parameters/Main.fib)
constructs this record at String and passes it to a generic appendWith. Tests
also instantiate it at Bool. It is an explicit first-class record dictionary,
not interface syntax, inferred implementation search, or a law certificate.

The type, constructor and optional eliminator receive the same ordered parameter telescope:
the erased type constructor, runtime constructor, and consuming eliminator.
For the example, calls explicitly supply A:

~~~text
AppendDictionary String
MkAppendDictionary String append ""
useAppendDictionary String motive dictionary branch
~~~

No implicit inference or quantity conversion is inserted. Parameter domains see
earlier parameters, not themselves/later ones; fields see all parameters, and
the second field additionally sees the first. Parameters must be distinct,
referenceable and explicitly quantity 0; field names may not shadow them.
Runtime or linear record parameters are not supported. These are type/index
parameters, not live constructor payloads.

Value indices and dependent parameter types are supported too:

~~~fibril
record Indexed (0 A : Type 0) (0 Family : (0 index : A) -> Type 0) : Type 0 where
  constructor MkIndexed
  eliminator useIndexed
  1 index : A
  1 value : Family index
~~~

The runnable example rebuilds such a value, preserving both linear fields. A
separate test uses an erased Bool parameter to choose String versus Bool payload
types. Wrong parameter arguments/field types and runtime use of an erased index
are rejected before effects.

Lowering uses existing Pi/lambda/application syntax and core checking; there are
no new core terms or unchecked constructor facts. Type/constructor global
references remain capture-resistant even when a parameter is named like its
record or constructor. All generated syntax is included in the existing
pre-clone admission estimate. Each record consumes two base declaration slots plus one for an explicitly requested eliminator, not one per parameter;
each requested projection consumes one additional slot. The original nonparameterized records are unchanged.

There is no universe polymorphism: the declared record universe still controls
the motive result universe, and Pi compatibility remains invariant. Parameter
and field declaration-site navigation inside record headers is still limited;
tooling does not invent spans for duplicated generated bodies.

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

## Optional named eliminators

The eliminator directive can be omitted for records and interfaces. There is no
generated hidden helper or fabricated helper token: only the type, constructor
and requested getters/method functions are emitted, checked and exposed as
symbols. Generated getters and typed patterns use core elimination directly.

~~~fibril
record Message : Type 0 where
  constructor MkMessage
  1 text : String

render : (1 message : Message) -> String
render = \(1 message : Message) => case message of (1 text : String) => text
~~~

[Minimal](../examples/modules/pattern-inference/Minimal.fib) combines this with
an interface without a named eliminator and prints No named eliminator needed!.
Keep an explicit eliminator directive when you want a reusable named dependent
elimination function or need to consume an entire wider telescope. Optional
naming does not introduce dot projections, automatic constructor naming, n-ary
patterns, or an implicit linear discard.

## Wider record representation and identity

![Bounded telescope lowering](diagrams/record-telescopes.svg)

The current identity decision is **transparent structural abbreviations**, not
generative nominal record types. Field and record spellings are not nominal
tags. Wider records with the same normalized ordered types/quantities remain
definitionally compatible; future nominal identity needs a kernel-level design
and rechecking, not elaborator metadata.

For fields f1 ... fn, n at least one, subject to resource admission:

- One field uses the quantity-aware [unary wrapper](unary-records.md), not Unit padding.

- Two fields keep exactly the original Sigma q r A B representation.
- Each preceding field lowers to Sigma q 1 A Tail. The tail is consumed once,
  irrespective of its fields' authored quantities.
- Constructors take all fields explicitly, in telescope order.
- Eliminators take an explicit record motive and one branch curried over all
  authored fields, with their original quantities.
- Each nested elimination reconstructs its enclosing pair in the erased motive.
  No eta law, quantity coercion or new core constructor is introduced.

Typed case syntax binds one unary field or two pair fields; use the
generated eliminator for a complete wider-record telescope. Requested getters
consume the whole record, and every nonselected field must permit zero use.
Each getter request consumes a declaration slot, not an eight-request quota.
Field/projection parsing uses fuel derived from the bounded input token stream;
type-expression depth remains bounded independently. Erased extraction depth is
derived from the telescope length, not hard-coded to eight.

Before generating expressions, a size-only calculation follows the constructor,
eliminator and getter recurrences. It uses dynamic programming for repeated
erased extractions instead of constructing exponentially repeated syntax just to
measure it. Admission has a cumulative 200000-node generated-IR budget per
elaboration call. A post-generation node-count check rejects an insufficient
estimate. This is distinct from the project's 200000-node expanded-core budget:
neither admission substitutes for checking.

Existing 65536-byte source, eight-parameter, 64-declaration, parser/checker depth
and reduction budgets remain. Thus arbitrary field counts are language syntax,
not a promise that every finite record compiles within the current resource
limits. API clients can lower the generated-IR allowance with
elaborateDeclarationsWithBudget; the CLI uses the default safety ceiling. These
are node/work admission policies, not allocation or wall-clock guarantees.

[Wider operational dictionaries](../examples/modules/wider-records/Main.fib)
prints Wider records! using a three-field parameterized operation/identity/label
dictionary. Its explicit append adapter bridges quantities without coercion.
This is operational data, not interface syntax or a proof of monoid laws.
[ManyFields](../examples/modules/wider-records/ManyFields.fib) demonstrates twelve
fields and prints Beyond eight fields!.

**Singletons are implemented using a proper unary wrapper.** Their constructor
and dependent eliminator preserve the field quantity without Unit padding or eta.
See [singleton rules, examples and evidence](unary-records.md). Empty records
remain rejected.

Regressions execute widths through sixteen, reject linear-field loss,
check a motive observing a reconstructed dependent record, sparse transitive
dependencies and extraction past field eight, wrong late payloads, nine getter
requests, structural compatibility, declaration limits and cumulative generated-IR
exhaustion. Syntax-only tools can inspect an oversized record without expanding it. They are tests,
not preservation or quantitative soundness proofs.

## Remaining record work

The constructor/eliminator core and resource-budgeted source record declarations
are in place, including erased parameter telescopes and explicit binary consuming
patterns. [Explicit interface declarations](explicit-interfaces.md) are now implemented;
next work includes interface constraints/selection, dot-field elaboration,
richer/inferred pattern syntax, nominality decisions, and richer visibility. Do not implement fst/snd by
silently discarding a linear component. The nesting policy above preserves existing two-field representations and uses
linear internal tails; generated eliminators preserve the authored field quantities.
Interfaces can then lower into those checked values. No automatic/dot-field projection, record eta, or dictionary inference is claimed yet.
