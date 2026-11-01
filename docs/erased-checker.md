# Experimental erased ordinary checker

Status: implemented prototype, **not the complete Fibril kernel**.

[Erased.idr](../src/Fibril/Core/Erased.idr) checks the ordinary Pi/lambda fragment
in erased mode. It supplies context formation, type inference, and checking
against a separately validated expected type.

## Supported rules

- Universe l has type Universe (l+1), with literal levels and upward universe compatibility.
- Pi formation checks both domains as types and takes the maximum level.
- Lambda inference checks its annotation and infers its body's type.
- Variable lookup shifts dependent domains into the current scope.
- Application weak-head exposes a Pi, checks the argument, and substitutes into its codomain.
- Sort inspection weak-head exposes a universe; full beta comparison remains separate.
- Checking normalizes inferred/expected types, then applies directional compatibility;
  literal universes lift upwards, while other types require equal normal forms.

Binder quantities remain in types and must match structurally during comparison.
No eta conversion, implicit quantity coercions, Pi covariance, or general
subtyping is provided. See [cumulativity scope](cumulativity-rewriting.md).

## Why erased first?

The checker allows type-only reasoning without consuming runtime resources.
It does not invoke runtime usage validation and does not return permission to
execute, duplicate, or erase values. A linear binder may be discarded in this
erased judgment; a future runtime judgment must separately reject invalid use.

This keeps the unresolved unrestricted/subusage policy out of the first checker.
It does not resolve quantitative cubical soundness.

## Entry points and budgets

- checkErasedContext validates the entire telescope.
- inferErased validates the context before inference.
- checkErased also verifies that the supplied expected type is itself a type.

Typing depth bounds recursive checking calls. Reduction fuel separately bounds
beta/unit-case contractions per normalization request. Neither budget bounds total time or memory.
CheckingLimit and ReductionLimit are explicit failures, distinct from actual type
mismatch. Repeated checks may repeat context validation and normalization; this is
reference code, not an optimized incremental elaborator.

The internal inference helper is private, so public callers cannot bypass context
formation merely by supplying a scope-correct telescope.

## Primitive Unit

The additional atomic rules are UnitType : Universe 0 and UnitValue : UnitType.
Both participate in the existing context-formation, compatibility, and scope
machinery. UnitCase additionally requires its scrutinee to have Unit type and
infers its body's type; conversion contracts a case on UnitValue. See [Unit](unit.md).

## Current trust boundary

No parser, declarations, general recursion, partial escape hatch, axioms, Void,
inductive definitions, path terms, composition, or Glue is implemented here.
No normalization, consistency, or checker-correctness proof is claimed.

The [ordinary checking plan](ordinary-checking.md) covers the broader intended
system. [ATKEY18](references.md#atkey18) motivates erased judgments, but this is
a small beta-only ordinary prototype, not a verbatim implementation of QTT or
the CCHM calculus.

## Validation

[Tests.Erased](../test/src/Tests/Erased.idr) checks polymorphic identity, dependent
application/lookup, beta conversion, universe separation, invalid contexts,
invalid expected types, quantity disagreement, and explicit budget failures.
Successful tests are not a metatheoretic proof.

[Constructive typing properties](../test/src/Tests/TypedProperties.idr) now test
acceptance, one-step preservation, identity-application conversion, and wrong
universe rejection over a bounded closed-term grammar. Expected types come from
generation recipes, not checker inference. This remains sampled evidence.

Next: expand dependent/open-context properties and design the runtime judgment
without conflating erased checking with resource-safe execution.
