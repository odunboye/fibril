# Constructor-named patterns and field inference

**Implemented prototype:** unary/binary record cases may name a transparent
constructor before their field binders. Field names can infer types and
quantities from that constructor; typed binders remain available. Motives may
be inferred or supplied.
The core still receives only the existing BoxCase/PairCase eliminations.

~~~fibril
case message of MkMessage (1 text : String) => text

case box of (MkBox String) (1 value : String) => value

case package of MkPackage (0 Item : Type 0) (1 value : Item) => value
~~~

[Named](../examples/modules/pattern-inference/Named.fib) runs a polymorphic unary
and genuinely dependent binary example and prints Named patterns!.

## Inferred field binders

~~~fibril
case box of (MkBox String) value => value
case package of MkPackage Item value => value
~~~

The constructor's checked signature supplies the complete field telescope,
including quantities and dependency of the second type on the first field.
The inferred erased Item is not runtime data; the inferred linear value still
cannot be dropped or duplicated. An unrestricted field may be reused.

[InferredFields](../examples/modules/pattern-inference/InferredFields.fib)
executes packaged payload recovery and a genuinely dependent family example,
printing Inferred payload! and Inferred family!.

Constructor type and canonical packing are validated before elaborating the
body under the inferred typed context. The final ordinary core checker remains
independent. The user-supplied field names are real lexical binders, with normal
shadowing and definition/reference targets; no source locations are guessed.

The inferred form accepts one or two names, all unannotated. The alternative
typed form accepts one or two fully typed binders. Mixed typed/untyped lists are
not supported. Duplicate names except wildcard _ reject; a wildcard does not
permit discarding a linear field.

## Parameters and syntax

A nonparameterized constructor can be a bare qualified or unqualified name.
For parameterized records, [bounded erased-prefix inference](pattern-parameters.md)
can recover arguments from the scrutinee type. Explicit parenthesized applications
such as (Data.Box.MkBox String) remain available for phantom parameters,
non-invertible families, inference limits, or explicit control.

Field quantities and types can be explicit or inferred from the constructor. Prefix resolution happens outside
the field binders, so a field cannot accidentally capture its constructor
reference. Ordinary lexical shadowing and direct-import/export visibility apply.
The grouped prefix must have a named function head, not an arbitrary anonymous
expression.

An explicit motive can still precede of:

~~~fibril
case message return (\(0 self : Message) => String)
  of MkMessage (1 text : String) => text
~~~

Unnamed typed cases remain supported. Nullary/n-ary constructor patterns,
nested patterns, alternatives, general implicit-argument inference and general inductive
coverage/refinement are not added.

![Named pattern validation](diagrams/constructor-patterns.svg)

## Validation, not an unchecked name decoration

[Expression.Constructor](../src/Fibril/Elaboration/Expression/Constructor.idr)
checks the constructor expression in the current typed context:

1. Infer its ordinary erased type.
2. Compare that type with the exact curried constructor type described by the
   typed fields and their Box/Sigma result. Quantities must match.
3. Apply the constructor to fresh scoped field variables and compare the result
   with the canonical annotated packing of those variables.
4. Reject different packing or bounded-comparison exhaustion.

The fresh-variable comparison is independent of the actual scrutinee's value.
A function that transforms or reorders fields does not qualify merely because
it agrees on one concrete input. A function with a matching type but a constant
packing body is rejected too.

After validation, contextual elaboration builds the ordinary explicit/inferred
motive case. The kernel independently checks actual scrutinee type, motive,
branch types and runtime usage. Name validation does not override those rules.

The constructor prefix is a **compile-time expression**, not an emitted runtime
call or runtime capture. Type-level evaluation is inert: no effect descriptions
execute. Original scrutinee/branch values retain their staged quantities and are
checked before runtime planning.

## Structural identity and aliases

This is not nominal constructor discrimination. Two transparent records with
equal normalized ordered types/quantities remain compatible. Consequently a
constructor of an identically shaped record can pass these checks. A
definitionally transparent constructor alias is allowed as well.

No registry asserts that a name originated from a record directive. Acceptance
means that the typed named function demonstrably packs its fresh arguments
canonically under the current bounded conversion rules. A local opaque function
variable does not pass just because its spelling shadows a known constructor.

Do not infer generative data identity, an abstraction boundary, an algebraic
law or general constructor coverage from this feature.

## Bounds and tooling

Constructor-type and packing comparisons use the existing type-reduction fuel
128 and checker depth 512. Inferred field domains have a combined 512-node
admission limit before constructing the branch. Oversized telescopes request
typed binders; this is an inference budget, not a restriction on field types. Exhaustion is an elaboration failure, not equality.
Project pre-clone estimates account for constructor validation expressions and
the bounded emitted motive. Existing source, parser, construction and checker
budgets apply; they are not allocation/time guarantees.

Syntax-only tools retain NConstructorCase and pending NPatternLambda name
binders without validating or inferring them. elaborate PATH
still reports checked: false and prints pending constructor-record-case IR.
Navigation traverses the prefix in the outer scope and targets its actual source
definition; branch variables retain their separate binder targets. Formatting
preserves constructor prefixes, explicit motives and authored field binders with
the usual reparse/shape guard.

Tests execute unary/binary/dependent and imported patterns, verify constructor
targets and formatter idempotence, and reject uninstantiated/wrong parameters,
wrong quantities, transformed or reordered packing, erased extraction, inferred
linear discard/duplication, field-count errors, unbound/private names and
opaque local shadows. Structural aliases are explicitly tested as accepted.
No kernel constructor, conversion rule or metatheoretic theorem is added.
