# Bounded motive inference for typed record patterns

**Implemented prototype:** unary and binary typed record patterns may omit the
return motive. Independent results get a constant motive; dependent results use
a canonical motive built from erased field extractions. Emitted terms still
contain explicit motives and are independently checked.

~~~fibril
recover : (0 A : Type 0) -> (1 box : Box A) -> A
recover = \(0 A : Type 0) => \(1 box : Box A) =>
  case box of (1 value : A) => value
~~~

Binary patterns retain both typed binders. Dependent packages now work too:

~~~fibril
recover : (1 package : Package) -> payloadType package
recover = \(1 package : Package) =>
  case package of (0 Item : Type 0) (1 value : Item) => value
~~~

[The simple example](../examples/modules/pattern-inference/Main.fib) prints
Inferred patterns!.
[The dependent example](../examples/modules/pattern-inference/Dependent.fib)
prints Dependent payload! and Dependent family!. Its second record contains
a type and a family indexed by that type; its inferred motive uses both field
extractions under result Pi binders.

Unnamed pattern domains and quantities remain explicit. [Constructor-named
patterns](constructor-patterns.md) can instead infer the complete field telescope
from an explicitly instantiated constructor, without nominal discrimination or
general inductive refinement.

![Contextual expression elaboration](diagrams/pattern-inference.svg)

## How inference works

The parser retains NInferCase with its arity, scrutinee and typed branch. It
does not manufacture a guessed result type. Syntax-only symbols, navigation,
formatting and named-IR inspection do not perform contextual inference.

[Elaboration.Expression](../src/Fibril/Elaboration/Expression.idr) tracks a scoped
typed context through explicit binders, typed lets and do statements:

1. Resolve the scrutinee and original branch, preserving global staging.
2. Infer the branch type with the existing erased checker.
3. Extract its result type after one or two field binders.
4. Bound and normalize **that type**, not the branch value.
5. If scope strengthening removes the fields, use a constant erased motive.
6. Otherwise substitute canonical erased field extractions for the field
   variables in the result type, preserving outer variables and inner binders.
7. Emit ordinary BoxCase or PairCase with the original scrutinee and branch.

The core independently verifies actual scrutinee shape, annotation domains,
exact field quantities, motive formation, branch type and runtime usage.
Pattern annotations and successful inference do not certify those facts.

A definitionally constant family can normalize away field dependence and use
the smaller constant motive. Result types can contain their own Pi binders;
scope transport and substitution preserve those binders.

## Canonical dependent motives

[Expression.Motive](../src/Fibril/Elaboration/Expression/Motive.idr) builds
ordinary typed eliminations, not primitive projections:

- Unary field extraction uses BoxCase.
- First-field extraction uses PairCase returning its first branch variable.
- Second-field extraction uses PairCase whose result type substitutes an
  erased first-field extraction into the dependent second domain.

The inferred motive replaces occurrences of the branch fields with those
extractions of its erased self parameter. For a reconstructed constructor,
the extraction reduces to the corresponding field. Thus branch compatibility
uses existing computation, not an eta rule or equality reflection.

All such extractions occur in types/motives. They may inspect erased fields
during erased checking but do not supply a public runtime getter or revive an
erased value. Original runtime branches remain unchanged and must use their
linear inputs exactly as checked.

This defines one canonical elaboration for this explicit unary/binary fragment,
not general motive search or proof-directed refinement. Structural records do
not gain nominal constructor identity from this rule.

## Explicit control and bounded expansion

Explicit return is still available for both unary and binary patterns:

~~~fibril
case tag return
  (\(0 self : Tag) => functionType self)
  of (0 Item : Type 0) => branch
~~~

It is especially useful when a compact explicit motive avoids repeating many
canonical projections in a large dependent function type. The test suite
includes a case where bounded inference rejects expansion but the explicit
motive checks and runs.

Checking depth 512 and type-reduction fuel 128 are unchanged; defaults live in
[Core.Limits](../src/Fibril/Core/Limits.idr), re-exported by Driver.Limits.
The inferred result type has a 512-node admission limit before and after
normalization. The substituted dependent motive body also has a 512-node limit.

Before substituting, a saturated weighted traversal estimates projection and
substitution tree sizes, accounting for occurrences under nested binders and
dependencies in the second domain. It rejects excess without constructing that
expanded tree; a post-count check detects insufficient estimates. Larger or
exhausted inference requests explicit return, never guessed success.

Project pre-clone admission reserves space for source branch annotations and
the generated motive, including its bounded body. The expanded-core post-count
check remains independent. Existing source/parser, generated-declaration,
checker and IO-plan limits still apply. These policies are not allocation or
wall-clock guarantees; reduction fuel alone does not bound term growth.

Inference failures carry the original case-expression point and elaboration stage.
Unbound names remain resolution failures. Ordinary core failures remain
unlocated unless the driver has a genuine declaration-policy point.

## Optional surface eliminator names

Records and interfaces may omit the eliminator directive. Typed patterns and
method/getter functions still elaborate to explicit core eliminations; no hidden
named function or fake source token is generated. Only an explicitly requested
helper consumes a third base declaration slot. The
[Minimal example](../examples/modules/pattern-inference/Minimal.fib) demonstrates
both record matching and an interface without named helpers. Wider consuming
operations can still request and call a named eliminator.

## API, evidence and remaining boundaries

Driver checking calls contextual expression elaboration directly.
[Source.Resolve](../src/Fibril/Source/Resolve.idr) remains a compatibility facade:
closed entrypoints supply an empty typed context; arbitrary untyped name-vector
entrypoints cannot infer motives without typed context.

Declaration elaboration remains earlier and separate. elaborate PATH reports
checked: false and preserves pending infer-record-case nodes, without import
resolution or contextual inference.

Tests cover independent and dependent unary/binary results, genuinely dependent
second domains, outer parameters and nested result binders, definitionally
constant families, type-level erasure versus runtime leaks, linear misuse,
explicit fallback after bounded expansion rejection, do contexts, binder
navigation, formatting/idempotence and execution after formatting.

The builders, scope transport and size estimator are untrusted elaboration
code; sampled tests and independent checking are not typed-substitution,
preservation or quantitative soundness theorems. No kernel constructor,
conversion rule or metatheoretic proof is added.

Unit matching remains case value of () => body; no dependent Unit eliminator
is introduced. Wider telescopes still use generated consuming eliminators.
Erased-constructor-parameter inference, expected-type-driven motive
selection, general inductive coverage/refinement and recursion termination
remain separate work.
