# Opt-in visible implementation lookup

## Use cases

Use `@{implementation}` at a concrete call site when you want the unique visible named implementation without spelling its qualified name repeatedly. For example, a String call and a Bool call can use the same generic algorithm with different checked dictionaries.

Prefer `@{Instances.Text.textSemigroup}` when behaviour should stay pinned as imports change, or when multiple implementations match. Use `@{}` for a generic function's local dictionary instead: global lookup is a different, explicit policy.

**Implemented prototype:** @{implementation} requests a unique already-checked
named implementation from the current module's earlier declarations and checked
direct imports:

~~~fibril
Algebra.concatThree String @{implementation} "Hello" ", " "interfaces!"
~~~

[The example graph](../examples/modules/visible-implementations/Main.fib)
runs String/Bool generic operations and a Monoid shape without naming their
implementation arguments at each ground call site.

![Visible provider selection](diagrams/visible-implementations.svg)

## Three distinct requests

- @{dictionary}: use that explicit expression.
- @{}: unique visible local dictionary, unchanged and with no global fallback.
- @{implementation}: unique visible named implementation global, independent
  of local candidates.

This is not automatic implicit application insertion, recursive instance search,
defaulting or a global coherence theorem. The source explicitly chooses the
lookup policy at each request.

Only closed checked named implementation declarations/blocks are eligible globals.
[Explicit parameterized factories](implementation-factories.md) are ordinary
exportable functions, not candidates for this lookup request.
An ordinary dictionary-shaped value is not automatically offered. Implementation
globals are unrestricted; erased and linear globals are not providers.

Own-module private implementations may be used by later own-module definitions.
Importers see only exported providers from checked direct dependencies.
Transitive reachability, private values and later declarations do not grant
visibility. A provider is published only after its defining declaration checks;
an imported module publishes nothing until all its declarations check.

## Identity and ambiguity

The compiler assigns an implementation a canonical module/name identity.
Its local and qualified aliases refer to one provider, not two candidates.
Two distinct implementation declarations remain two candidates even if their
values normalize identically.

Matching uses exact bounded conversion of the required dictionary type.
No type parameters are invented and no implementation-producing function is
instantiated. Missing, ambiguous or inconclusive lookup fails with a source
selection point and asks for an explicit dictionary.

Interface identity is [nominal](nominal-interfaces.md): two interfaces with equal method
types are different types, so a provider matches only its own interface. Plain
records stay structural, and a record is not accepted where an interface is
expected. No algebraic-law certificate is implied. Uniqueness in this visibility snapshot is not whole-
program semantic coherence. Adding a direct import can introduce ambiguity,
which is rejected rather than resolved by declaration/import order.

## Checking, staging and bounds

The selected occurrence uses the same declared-signature-preserving wrapper as
ordinary global lookup. Its original value is not normalized before ordinary
runtime checking. No erased data is revived and no effect executes during
selection; IO planning remains separate.

Provider metadata in [Source.Global](../src/Fibril/Source/Global.idr) is ordinary
data, not a typing certificate. Compatibility Global/GlobalWithQuantity
constructors do not opt ordinary globals into lookup. The project driver tags
named implementations only after checking their type, value, quantity and
structural dictionary shape.

Selection visits a finite list of visible closed providers and compares types
with the existing reduction fuel 128. It does not recursively construct more
dictionaries. Project pre-clone admission reserves the largest visible provider
occurrence before selection can copy it; the independent expanded-core
post-count check remains in force. This can be conservative. These budgets are
not allocation or wall-clock guarantees.

Syntax-only tools retain implementation-apply IR. elaborate PATH remains
unchecked and does not perform lookup. Automatically chosen providers have no
invented source reference token; use an explicit @{Qualified.name} when a
navigable provider name is desired.

Tests cover own/imported selection, alias deduplication, distinct equal-valued
providers, ambiguity/explicit choice, ordinary-value exclusion, missing lookup,
exact selector locations, private/transitive visibility and rejection of invalid
providers before output. Existing local-only lookup tests remain unchanged.

No kernel term, conversion rule, recursive resolution or soundness theorem is
added. Automatic factory resolution, overlapping priorities, anonymous constraint
insertion, inheritance, symbolic operators and law evidence remain separate work.
[Named infix calls](infix.md) can now use this explicit lookup request in their
quoted function application.
