# Explicit parameterized implementation factories

## Use cases

Use an implementation factory when a reusable data wrapper should obtain its
operations from operations supplied for its contents. For example, combine two
Box A values by unpacking them, combining the A values with the caller's
Semigroup A dictionary, and repacking the result. One factory then works for
String and Bool without duplicating the wrapper's method implementation.

This adds named-method-block convenience and implementation classification to
ordinary functions returning dictionaries. It is not new computational power:
an ordinary function with explicit constructor applications remains an
alternative. For a single concrete implementation, a non-parameterized block is
simpler. For arbitrary runtime configuration arguments, use an ordinary function;
implementation factories admit erased parameters and runtime dictionaries.

**Implemented prototype:** explicit factory application, with no recursive
instance search, implicit parameter inference, law checking or new kernel rule.

![Implementation factory lowering](diagrams/implementation-factories.svg)

## Example: reuse operations through a wrapper

The checked [BoxOps module](../examples/modules/implementation-factories/BoxOps.fib)
declares a one-field Box and a factory:

~~~fibril
implementation boxedSemigroup : (0 A : Type 0) ->
  (ops : Algebra.Semigroup A) => Algebra.Semigroup (Box A) where
  combine = \(1 left : Box A) => \(1 right : Box A) =>
    case left of MkBox first =>
      case right of MkBox second => MkBox A (first `Algebra.combine A @{}` second)
~~~

The type parameter A and dictionary ops are bound by the implementation header
and are available in method bodies. The block generates ordinary typed lambdas
around a checked constructor application. Method order is still schema-guided;
missing, duplicate and unknown methods remain errors. Methods do not become
mutually recursive local bindings.

The block's final result must directly name a visible interface with its
arguments explicit. Header continuations must be indented, and where must end
its line. The final interface schema still comes from an earlier local interface
or an exported interface in a checked direct dependency.

The [entry program](../examples/modules/implementation-factories/Main.fib)
supplies the factory explicitly:

~~~fibril
Algebra.combine (BoxOps.Box String)
  @{BoxOps.boxedSemigroup String @{implementation}}
  (BoxOps.MkBox String "Hello, ")
  (BoxOps.MkBox String "factories!")
~~~

Here the inner @{implementation} selects a closed Semigroup String dictionary.
The explicitly named boxedSemigroup transforms it into a Semigroup (Box String).
The outer explicit dictionary argument supplies that result to combine.
Unpacking the resulting Box prints Hello, factories!. A second call instantiates
the same factory for Bool and prints Reused Bool operations!.

Semigroup is an operation shape here: these examples do not certify
associativity, and the Bool/NAND implementation is deliberately not such a proof.

## Expression form and parameter policy

The explicit dictionary expression form also supports factories:

~~~fibril
implementation forwarded : (0 A : Type 0) ->
  (ops : Algebra.Semigroup A) => Algebra.Semigroup A
forwarded = \(0 A : Type 0) => \(ops : Algebra.Semigroup A) => ops
~~~

Factory signatures may have erased parameters and runtime dictionary-shaped
parameters, ending in a Box/Sigma dictionary type. The ordinary independent
checker validates all domains, result formation, quantities and the value.
Runtime domains that are not dictionary-shaped are rejected for named factories;
an ordinary function is the fallback. Erased constraint-arrow syntax is still
unsupported; existing ordinary erased parameters retain their normal rules.

The implementation global itself remains unrestricted. This does not weaken its
parameters: an unrestricted method closing over a linear dictionary can demand
repeated use of that dictionary and is rejected. Erased parameters cannot be
revived as runtime values.

## Lookup and visibility

Factories are not published as closed providers. @{implementation} still visits
only closed checked named dictionary values; it never instantiates this factory
or recursively builds its dependencies. Select a factory by name, supply its
arguments explicitly, then pass its result through @{expression}.

Exported factory functions obey ordinary direct-import visibility. The block's
header parameter scope ends with its methods and does not leak into following
declarations. Explicit references in methods navigate to the real header binder
rather than a fabricated generated lambda token.

## Admission and evidence

Generated-IR preflight includes every copied parameter domain and lambda. An
independent post-generation count checks the estimate. Existing cumulative
construction/core admission and checker depth/reduction budgets still apply.
Signature traversal is depth-bounded. These are work policies, not a verified
erasure, normalization, stack or allocation theorem.

Tests cover String/Bool instantiation, explicit-expression factories, multiline
headers, formatting/idempotence, header-binder navigation, exclusion from closed
provider lookup, linear/erased misuse, runtime non-dictionary parameters and
invalid methods. Syntax-only elaborate remains unchecked; imported schemas are
still unavailable to local-only elaborate PATH.

**Remaining:** automatic/recursive factory resolution, inferred factory arguments,
parameterized law evidence and global coherence need separate designs.
