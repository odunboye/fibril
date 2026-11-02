# Bounded motive inference for typed record patterns

**Implemented prototype:** unary and binary typed record patterns may omit the
return motive when the branch's inferred result type is definitionally
independent of the pattern-bound fields. The emitted core still contains an
explicit erased motive and is independently checked.

~~~fibril
recover : (0 A : Type 0) -> (1 box : Box A) -> A
recover = \(0 A : Type 0) => \(1 box : Box A) =>
  case box of (1 value : A) => value
~~~

A can depend on outer erased parameters; it must not depend on the newly
introduced value binder. Binary patterns retain both typed field binders:

~~~fibril
render : (1 message : Message) -> String
render = \(1 message : Message) =>
  case message of (1 enabled : Bool) (1 text : String) =>
    if enabled then appendString text "!" else text
~~~

[The runnable example](../examples/modules/pattern-inference/Main.fib) prints
Inferred patterns!. Pattern domains and quantities remain explicit; there is no
constructor-name matching or inferred field-type annotation.

![Contextual expression elaboration](diagrams/pattern-inference.svg)

## How inference works

The parser retains NInferCase with its arity, scrutinee and typed branch. It
does not manufacture a guessed result type. Syntax-only symbols, navigation,
formatting and named-IR inspection do not perform this inference.

[Elaboration.Expression](../src/Fibril/Elaboration/Expression.idr) tracks a scoped
typed context through explicit binders, typed lets and do statements:

1. Resolve the scrutinee and original branch, preserving global staging.
2. Infer the branch type with the existing erased checker.
3. Extract its result type after one or two field binders.
4. Bound and normalize **that type**, not the branch value.
5. Remove the pattern variables by partial scope transport. Dependence on any
   removed variable is an error, including occurrences under nested binders.
6. Build a constant motive over the unary/pair type described by the pattern.
7. Emit ordinary BoxCase or PairCase with the original scrutinee and branch.

The core independently verifies the actual scrutinee shape, annotation domains,
exact field quantities, motive formation, branch type and runtime usage.
Pattern annotations do not assert those facts. Inference acceptance alone is
not publication or a checking certificate.

A definitionally constant family can normalize away a field occurrence in the
result type. A genuinely dependent result cannot. Result types may contain
their own Pi binders: scope transport preserves these while rejecting forbidden
references to the outer pattern fields.

## Dependent results retain explicit motives

For an erased wrapped type, a branch returning an identity at that type has a
result depending on the bound Item. Omitted return produces:

~~~text
Dependent pattern result requires an explicit return motive
~~~

The explicit unary form is now supported too:

~~~fibril
case tag return
  (\(0 self : Tag) => ((1 x : itemType self) -> itemType self : Type 1))
  of (0 Item : Type 0) => \(1 x : Item) => x
~~~

Binary explicit motives remain unchanged. Unit matching remains
case value of () => body; this does not add a dependent Unit eliminator.
For wider record telescopes use the generated consuming eliminator.

This slice does not infer dependent substitutions, motives from an expected
function result, constructor patterns, branch refinement, coverage or recursion
termination. It is deliberately narrower than Idris 2 dependent matching.

## Resource and diagnostic boundary

Checking depth 512 and type-reduction fuel 128 are unchanged; defaults now live
in [Core.Limits](../src/Fibril/Core/Limits.idr), re-exported by Driver.Limits.
An inferred result type has a 512-node admission limit before and after
normalization. Larger types and exhausted normalization require an explicit
return motive, not guessed success.

Project pre-clone admission reserves space for both the source branch annotations
and the generated motive, including its maximum result-type size. The existing
expanded-core post-count check remains independent. Existing source/parser,
generated-declaration, checker and IO-plan limits still apply. These policies
are not allocation or wall-clock guarantees; reduction fuel alone does not
bound term growth.

Failures from contextual inference carry the original case-keyword point and
the elaboration stage in human/version-2 JSON diagnostics. Ordinary unbound
names remain resolution failures; ordinary core checking failures remain
unlocated unless the driver has a genuine declaration-policy point.

Erased fields cannot become runtime data; linear fields cannot be dropped or
duplicated; ambient captures still combine normally. Inference never normalizes
the original branch before runtime checking or executes an effect description.

## API and evidence

Driver checking now calls contextual expression elaboration directly.
[Source.Resolve](../src/Fibril/Source/Resolve.idr) is a compatibility facade.
Closed compatibility entrypoints use an empty typed context; arbitrary
name-vector entrypoints remain lexical and cannot infer motives without typed
context. Existing explicit expressions continue to resolve there.

Declaration elaboration remains a separate earlier pass. elaborate PATH still
reports checked: false and leaves pending infer-record-case nodes in named IR;
it does not resolve imports or run contextual expression inference.

Tests cover unary/binary execution, outer polymorphic types, result Pi binders,
definitionally constant families, erased extraction and linear misuse rejection,
dependent failure/explicit fallback, typed do contexts, actual binder navigation,
formatter idempotence and scope transport. The transport utility is untrusted
elaboration code, not a typed substitution theorem. No new kernel term,
conversion rule or metatheoretic proof is introduced.
