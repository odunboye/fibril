# Erased constructor-parameter inference in patterns

## Use cases

Use erased-prefix inference to avoid repeating a constructor's type/index arguments when the scrutinee type already determines them. This makes a pattern such as `case box of MkBox value => value` practical.

Supply arguments explicitly for phantom or otherwise noninvertible parameters. This feature recovers information in patterns; it does not infer arbitrary omitted arguments in ordinary constructor calls.

**Implemented prototype:** constructor-named unary/binary record patterns may
omit a leading erased constructor prefix when its arguments can be recovered by
bounded structural matching against the scrutinee's checked type.

~~~fibril
case box of MkBox value => value
case pair of MkBoth left right => body
~~~

[InferredParameters](../examples/modules/pattern-inference/InferredParameters.fib)
runs a polymorphic unboxer whose outer A is recovered from Box A and prints
Inferred parameters!. Tests also infer two different type parameters for one
binary constructor.

This is selective pattern elaboration, distinct from the [bounded direct-global implicit argument slice](implicit-arguments.md); neither is general implicit argument inference,
instance search, higher-order unification, expected-type-driven refinement,
or nominal constructor identity. Ordinary constructor applications still take
their explicit arguments, for example MkBox String "value".

![Pattern parameter inference](diagrams/pattern-parameters.svg)

## Algorithm and trust boundary

[Expression.Parameters](../src/Fibril/Elaboration/Expression/Parameters.idr):

1. Infers the constructor signature and counts its curried Pi telescope.
2. Treats the excess over the supplied field-binder count as a candidate
   parameter prefix; every such binder must be erased.
3. Opens that prefix with elaborator-only metavariable identities, and opens
   field binders without treating their values as inferable parameters.
4. Bounds and normalizes the residual constructor result type and actual
   scrutinee type.
5. Structurally matches them, collecting consistent parameter solutions.
6. Rejects unsolved/conflicting constraints, escaping local variables or
   exhausted work bounds.
7. Applies the recovered erased arguments to the original constructor term.

Only then do existing constructor-type/canonical-packing validation, field
inference and motive elaboration proceed. The emitted BoxCase/PairCase still
goes through independent ordinary core checking.

Metavariables live in the elaborator's scope map, **not in core terms**.
Solutions are ordinary scoped terms from the scrutinee type; they cannot contain
new unsolved metavariables. No axioms, guessed type inhabitants or unchecked
generated definitions are installed. Applying the inferred arguments rechecks
their kinds and dependent parameter domains through ordinary erased checking.

## Supported constraints

Parameters occurring directly in normalized structural types can be solved.
Repeated occurrences must agree under bounded conversion. Matching descends
under Pi/lambda/Sigma binders without allowing a solution to capture a variable
local to the matched type. Outer context variables, including an erased
polymorphic A, remain available.

An ordinary structural record alias is enough; no separate constructor registry
or nominal class metadata is used. Existing structural identity and transparent
constructor-alias rules remain unchanged.

Some useful function-valued solutions may be recovered when they occur directly.
The algorithm does not invert applications, synthesize lambdas from pointwise
constraints or solve arbitrary higher-order equations.

## Explicit fallback

Parameters absent from the normalized representation are phantom and cannot
be recovered:

~~~fibril
case phantom of (MkPhantom Bool) value => value
~~~

A parameter hidden behind a non-injective computational family also requires
explicit input. For example, if a Bool index selects String or Bool, the matcher
does not infer True merely from seeing String:

~~~fibril
case indexed of (MkIndexed True) value => value
~~~

Explicit constructor applications remain supported, including partially
instantiated prefixes whose remaining arguments are inferable. Inconsistent
constraints or an incorrect constructor still fail; supplying arguments is not
an escape from type/quantity checking.

Both field-name-only and typed field lists can use parameter inference.
Field inference, parameter inference and motive inference have separate roles
and bounds. Constructor-name resolution and original scrutinee/branch staging
remain intact; an erased scrutinee cannot become runtime data through type
normalization.

## Bounds, tooling and evidence

Signature peeling uses checker-depth 512 and bounded type exposure. Matching
types are limited to 512 nodes before and after normalization; normalization and
solution-consistency comparisons use fuel 128. Inferred arguments plus their
application nodes have a combined 512-node limit. Inference requests explicit
arguments when those bounds are exceeded; it does not claim uninhabitability.

Project pre-clone admission reserves space for inferred prefix arguments and
their constructor-validation copies. Field/motive bounds, expanded-core
post-count checks and existing source/checker limits remain independent.
These bounds are not a wall-clock or allocation theorem.

Syntax-only tools retain the authored bare constructor and do not invent source
tokens for inferred arguments. elaborate PATH remains unchecked and leaves
contextual inference pending. Definition/reference targets continue to use the
real constructor and field tokens.

Tests exercise outer polymorphism, multiple and repeated parameters, typed and
untyped fields, imported constructors, phantom/indexed explicit fallback,
inconsistent constraints, local-variable escape rejection, erased scrutinee
misuse, inference admission and formatter idempotence. No kernel term,
conversion rule, coverage rule or soundness theorem is added.
