# Source data and named elimination

## Use cases

**Implemented prototype:** declare a finite choice of constructors with checked
payloads. Optional A expresses absence/presence without a dummy value; a Result
shape can carry an error or a successful value. A constructor can carry several
dependent fields. Prefer a record when all fields are present together, Bool for
an uninformative decision, and direct values when no alternative is needed.

Most of this page describes non-recursive data. A separate, deliberately
restricted [recursive declaration slice](#unary-recursive-declarations) supports
one terminal and one direct linear self field; a [parameterized list shape](#parameterized-list-shape)
also carries a linear element. A built-in [Nat recursor](nat-recursion.md)
supports structural computation. General recursive data, general strict
positivity and indexed constructor refinement remain future work; recursive
function equations are covered by the structural forms and by
[general recursion](function-equations.md#general-recursion). [Direct multi-branch cases](direct-data-cases.md)
support zero- and one-field alternatives and the fixed list head/tail shape,
including qualified direct imports; general wider patterns remain future work.

![Source data lowering](diagrams/source-data.svg)

## Declare and construct

~~~fibril
module Example

data Optional (0 A : Type 0) : Type 0 where
  eliminator useOptional
  Nothing : Optional A
  Just : (1 value : A) -> Optional A
~~~

Headers are column-one, single-line data Name parameters : Type [n] where;
[bare Type](bare-type.md) denotes Type 0.
Parameters must be explicitly erased, uniquely named and referenceable.
Constructor signatures are aligned indented single lines, with named typed
field binders followed by the data type applied to all parameters in order.
Fields may depend on earlier fields. Their quantities are explicit or use the
existing unrestricted default. Anonymous constructor arrows, recursive payloads,
forward dependencies, alternative result targets and index refinement are not
accepted in this slice.

There is no fixed constructor or field count cap for data. Explicit-parameter
data has no separate parameter count cap; an implicit constructor prefix admits
at most 64 parameters. Source, declaration-slot, generated-IR, expanded-core,
depth and reduction budgets still apply. Wide declarations can be admitted while a larger requested eliminator
exhausts conversion fuel; omitting that helper does not remove the other checks.

With parenthesized headers, constructors are ordinary functions with explicit
zero-quantity parameters, preserving existing source:

~~~fibril
Nothing String
Just String "present"
~~~

A data header can instead opt its generated constructors into implicit erased
parameters. The braces describe **constructor visibility**, not a change to the
data family's own explicit parameters:

~~~fibril
data Choice {0 A : Type} {0 B : Type} : Type where
  Left : (1 value : A) -> Choice A B
  Right : (1 value : B) -> Choice A B

sample : Choice String Bool
sample = Left "receipt"                 -- B comes from the expected result
explicit : Choice String Bool
explicit = Left {String} {Bool} "receipt"
~~~

Use either all braces or all parentheses in one data header; mixed modes are not
supported. The family remains `Choice String Bool`, and an optional eliminator
still takes explicit parameters. Constructor fields retain their declared
quantities. Existing direct cases name the constructors without braces and compare
against checked constructor values, not authored layout hints. A single unary
branch is parsed as a record pattern rather than a direct data case; use an
eliminator for that form. General indexed constructor refinement and wider direct
patterns remain unsupported. A nullary constructor has no ordinary argument to
trigger insertion: write e.g.
`None {String}`; a bare `None` remains an uninstantiated value. See the
[implicit-constructor example](../examples/modules/implicit-constructors/Main.fib)
and [inference contract](implicit-arguments.md). Scoped structural inference is
not complete, and ambiguous or exhausted cases require explicit braces.

An export marker on the data declaration exports its type, constructors and
requested helper; otherwise the bundle is private. Other modules must directly
import the defining module; unique imported names can be used unqualified, while
ambiguous ones require qualification. Dependencies must check
completely, including unused/private generated bodies, before publishing exports.

## Unary recursive declarations

A parameterless `Type 0` data declaration can have exactly one terminal
constructor and one constructor with exactly one **linear direct self field**:

~~~fibril
data Chain : Type where
  eliminator foldChain
  Empty : Chain
  More : (1 rest : Chain) -> Chain

marks : (1 chain : Chain) -> String
marks chain = foldChain (\(0 self : Chain) => String) ""
  (\(0 rest : Chain) => \(1 result : String) => appendString result "!") chain
~~~

The [runnable import example](../examples/modules/recursive-data/Main.fib)
prints `!!`. Constructor order can be reversed. The optional named fold accepts
an erased dependent motive, a linear terminal result, an unrestricted step and a
linear scrutinee. Its step receives the recursive tail **erased** for the motive
and the recursively computed result **linearly**; it cannot inspect the tail at
runtime. A step that may execute repeatedly cannot capture ambient linear data.
Omitting the `eliminator` directive emits no helper.

This is genuine structural recursion over the actual tail, not a Nat-backed
encoding: a finite core type carries its qualified identity and an intrinsic
fixed terminal/linear-self shape. The core independently checks constructors,
motives, both fold cases and resource use. Its recursive computation descends
only into the stored tail. The shape is strictly positive **by construction**;
there is no general positivity checker or recursive declaration environment.
Lowering reserves 64 generated-IR nodes without the helper or 512 with it before
constructing the fixed templates, then checks their actual size; existing source,
module-expansion, checking and reduction admissions also apply. These are not
hard time, stack or allocation guarantees. Nested/mutual recursion, arbitrary
payload fields, indexed recursive families and more constructors remain
unsupported. Equations over this family that are not structural, such as
[stepping down two links](../examples/modules/general-recursion/Chain.fib), use
[general recursion](function-equations.md#general-recursion). Direct `case` can inspect this unary
family once and exposes its actual tail linearly. Use the named fold for
structural recursion, or the [restricted structural equation form](function-equations.md#structural-unary-data-equations)
with an optional uniform erased/unrestricted prefix when its syntax applies. The experimental C backend supports these
fixed forms with separate native runtime budgets.

![Unary recursive data checking](diagrams/recursive-data.svg)

## Parameterized list shape

A second fixed positive shape supports a useful `List A`-style type:

~~~fibril
data Items {0 A : Type} : Type where
  eliminator foldItems
  Empty : Items A
  Prepend : (1 head : A) -> (1 tail : Items A) -> Items A
~~~

The [runnable imported example](../examples/modules/recursive-list/Main.fib)
uses `Prepend "hello" ...`, an explicit `Empty {String}`, and `foldItems String`
to print `hello world`. Parenthesized `(0 A : Type)` headers retain explicit
constructor arguments instead. The type family and fold parameters remain
explicit in either spelling.

The accepted form has exactly one erased `Type 0` parameter, one nullary
constructor, and one constructor whose fields are exactly a linear element of
that parameter followed by a linear direct self tail with the **same** parameter.
Both constructor orders are accepted. The dependent fold's step takes the
head linearly, the actual tail erased and the recursive result linearly. The
step itself is unrestricted because it can execute repeatedly; capturing a
linear resource or discarding the linear head/result is rejected. Core checking
retains both the qualified family key and the element type, so two list families
or incompatible element types are not interchangeable.

The shape is positive by construction; this is not arbitrary recursive data or
a general positivity checker. Extra payloads, dependent field telescopes,
multiple parameters or indices, nonuniform recursion and nested/mutual recursion
remain unsupported. Direct `case` inspects one layer with a linear head and
linear tail. For recursion, use the named fold or the restricted
[list-shaped equation form](function-equations.md#structural-list-shaped-equations)
with a bounded erased/unrestricted prefix telescope whose recursive arguments
stay unchanged. The generated
fixed templates reserve 128 nodes without the fold or 768 with it before named-IR
construction and are post-counted; these are admissions, not hard resource
bounds. The experimental C backend also supports these fixed recursive values,
cases and folds, subject to its own limits.

## Use the optional eliminator

The eliminator directive is optional and appears before constructor signatures.
Omitting it emits no helper, fake symbol, binding slot or helper construction
cost. A requested helper takes parameters, an erased dependent motive, a linear
scrutinee, then one branch per constructor in declaration order.

~~~fibril
fromOptional : (0 A : Type 0) -> (fallback : A) -> (1 item : Optional A) -> A
fromOptional = \(0 A : Type 0) => \(fallback : A) => \(1 item : Optional A) =>
  useOptional A (\(0 self : Optional A) => A) item fallback (\(1 value : A) => value)
~~~

[The runnable graph](../examples/modules/data/Main.fib) prints:

~~~text
present
missing
dependent package
~~~

The third line uses an imported constructor containing an erased type, a renderer
for that type, and a linear payload. See [Package](../examples/modules/data/Package.fib).
Its generated dependent eliminator unpacks the telescope without an eta rule.

**Branch permission limitation:** named helper branch arguments are unrestricted.
They can be closed values/functions or capture unrestricted ambient inputs;
their own payload binders still have the declared quantities. Passing a branch
that captures an ambient linear value is rejected. A curried ordinary Pi type
does not express the additive sharing between alternatives that direct kernel
cases support. The helper does not weaken linearity to approximate that feature.
[Direct source cases](direct-data-cases.md) now permit this additive sharing for
nullary/unary non-recursive constructors, unary recursive families and the fixed
list-shaped head/tail family with an explicit or inferred motive.

### Staged case-metadata boundary

The module checker now retains exported authored data-layout hints after all
module declarations have checked. The hints preserve the defining module,
constructor order, field quantities/types and authored spans; private data is not
published. They are ordinary untrusted metadata, not certificates. The new
source cases compare checked global values with the actual inferred nominal shape;
they do not consume these hints as typing authority. A bounded `planDataArms` helper now rejects missing, duplicate or unknown
constructor names and wrong field arities, returning indices in declaration
order. `selectDataImports` filters a supplied module inventory by explicit direct
imports and rejects missing/ambiguous inventories or mismatched origins. Both
operate on ordinary untrusted data; they neither establish constructor identity
nor type-check branch bodies. These helpers are not wired into the expression
driver yet. An internal `assembleDataCase` helper builds the raw direct
`NominalCase`/`VariantCase` candidate from an explicit motive, shape and already
positional branches. The ordinary checker must still validate the entire term;
source elaboration now supplies zero/unary payload binders and explicit or inferred motives.
`assemblePairPayloadBranch` constructs a candidate PairCase around an explicit
curried two-field branch; its dependent pair type, motive and tag are untrusted.
The core checker still checks quantities, domains and branch type. Tests cover
two linear String fields, wrong tags, dropped fields, dependent motives, branch
omission and joined ambient linear demand. Dependent *field telescope* handling
is not yet demonstrated by this builder's tests.
The [direct case frontend](direct-data-cases.md) now uses this candidate builder
and ordinary independent checking. Qualified direct-imported patterns now use
checked visible globals too; wider dependent field telescopes and general-purpose expected-type propagation remain future work. The older pure metadata
planning helpers remain unused by the direct-case driver.

### A reusable, non-Church Sum

The separately packaged [Data.Sum](../examples/packages/sum-library/src/Data/Sum.fib)
declares `Sum A B`, `Left` and `Right` using the checked data prototype, then
provides an ordinary `fold` over its generated `useSum` eliminator. Its
[authored test suite](../examples/packages/sum-library/src/Data/Sum/Tests.fib)
checks both constructors and can run offline:

~~~sh
fibril check --package examples/packages/sum-library/fibril.yaml
fibril test --package examples/packages/sum-library/fibril.yaml
~~~

This avoids encoding the choice as a function and is reusable through an explicit
local package dependency. `fold` is a convenience wrapper, not new language power:
it retains the helper's unrestricted-branch/linear-capture limitation. Prefer Bool
for a choice with no payload, Optional for a single optional payload, or a record
when both fields are present. The suite samples cases; it is not a soundness proof.

The helper's motive returns the declaration's literal universe. For a Type 1
data declaration and a String result, the example explicitly ascribes the motive
body as (String : Type 1). Literal universe compatibility is not propagated
through Pi conversion. The named helper still needs an explicit motive; direct cases also support [bounded motive inference](data-motive-inference.md).

## Nominal identity and lowering

Qualified module/type keys distinguish equal-shaped declarations. All parameter
arguments are retained, including phantom ones, so Flag String and Flag Bool
remain distinct. This does not change structural record/interface identity and
does not certify payload validation or algebraic laws.

Parsing retains authored data/constructor/field tokens. Declaration elaboration
builds named IR using internal nominal/variant nodes; those nodes have no general
source expression syntax. It then uses ordinary contextual expression elaboration
and independent core checks for the type, every constructor and the helper.
A name or imported schema does not grant typing authority.

- Nullary arms have no payload or hidden Unit padding.
- One-field arms retain the field's type and quantity directly.
- Wider arms carry a linear existing dependent Sigma telescope, preserving each
  field quantity and the existing consuming record machinery.
- The erased family body has an explicit universe ascription before parameters
  close, preserving its declared level without changing conversion.
- Constructor results use declared-signature-preserving global occurrences.
- Optional elimination composes consuming NominalCase/VariantCase with checked
  telescope elimination; generated definitions are not trusted reductions.

Size-only preflight accounts for all copied shapes, fields, binders, indices and
helper motives before generation. A post-generation count guards the estimate;
project core pre-clone admission and independent post-counting still apply.
These are work policies, not time/allocation guarantees or a soundness theorem.

## Source services and evidence

Definitions/symbols use actual type, constructor, parameter, field and helper
names. Generated branch binders have no invented authored navigation target.
Formatting preserves data shape under reparse/AST guards and does not yet wrap
long constructor signatures. Vim/Neovim and handbook highlighting recognize data.
elaborate PATH displays unchecked named IR, including pending kernel forms;
it does not certify a declaration.

CLI tests run Optional and imported dependent packages, inspect IR, format and
re-execute, follow constructor/dependent-field definitions, reject nominal/phantom
mixups, bad targets, recursion/forward references, duplicates and shadowing, and
admit nine parameters, sixteen alternatives and sixteen constructor fields under
existing budgets. The kernel tests/proofs remain distinct from typed preservation,
canonicity, positivity, termination and verified erasure.

Next: extend direct cases to dependent multi-field patterns,
then the separate recursive-inductive and termination milestones in the [landing plan](inductive-data.md).
