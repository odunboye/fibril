# Non-recursive source data and named elimination

## Use cases

**Implemented prototype:** declare a finite choice of constructors with checked
payloads. Optional A expresses absence/presence without a dummy value; a Result
shape can carry an error or a successful value. A constructor can carry several
dependent fields. Prefer a record when all fields are present together, Bool for
an uninformative decision, and direct values when no alternative is needed.

This is non-recursive data, not yet general inductive data. Nat/List recursion,
strict positivity, indexed constructor refinement, recursive functions and source
multi-branch case syntax remain future work. Existing record cases do not become
data cases by spelling a data constructor name.

![Source data lowering](diagrams/source-data.svg)

## Declare and construct

~~~fibril
module Example

data Optional (0 A : Type 0) : Type 0 where
  eliminator useOptional
  Nothing : Optional A
  Just : (1 value : A) -> Optional A
~~~

Headers are column-one, single-line data Name parameters : Type n where.
Parameters must be explicitly erased, uniquely named and referenceable.
Constructor signatures are aligned indented single lines, with named typed
field binders followed by the data type applied to all parameters in order.
Fields may depend on earlier fields. Their quantities are explicit or use the
existing unrestricted default. Anonymous constructor arrows, recursive payloads,
forward dependencies, alternative result targets and index refinement are not
accepted in this slice.

There is no fixed constructor, field or parameter count cap for data. Source,
declaration-slot, generated-IR, expanded-core, depth and reduction budgets still
apply. Wide declarations can be admitted while a larger requested eliminator
exhausts conversion fuel; omitting that helper does not remove the other checks.

Constructors are ordinary functions with explicit erased parameters:

~~~fibril
Nothing String
Just String "present"
~~~

An export marker on the data declaration exports its type, constructors and
requested helper; otherwise the bundle is private. Other modules must directly
import the defining module and use qualified references. Dependencies must check
completely, including unused/private generated bodies, before publishing exports.

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
Direct multi-branch surface cases are a later slice.

### Staged case-metadata boundary

The module checker now retains exported authored data-layout hints after all
module declarations have checked. The hints preserve the defining module,
constructor order, field quantities/types and authored spans; private data is not
published. They are ordinary untrusted metadata, not certificates: no current
expression consumes them and they do not implement case syntax or change type
checking. Same-module incremental visibility, direct-import selection, ambiguity,
substitution, resource admission and independently checked case lowering remain
future work. This internal staging adds no language power or user-facing syntax.
Until then, use the explicit eliminator or the Sum wrapper below.

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
through Pi conversion. Use an explicit motive; no data-motive inference is added.

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

Next: exhaustive flat data cases with direct branch resource joins, then the
separate recursive-inductive and termination milestones in the [landing plan](inductive-data.md).
