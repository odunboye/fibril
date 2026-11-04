# Constant motives for direct data cases

## Use cases

**Implemented:** omit `return` in a supported direct data case when the branches
have one inferable, non-payload-dependent result type. This is useful for a
request renderer with both nullary and unary alternatives:

~~~fibril
render : (1 prefix : String) -> (1 request : Request) -> String
render prefix request = case request of
  Health => prefix
  Preview subject => appendString prefix subject
~~~

See the runnable [function-equations example](../examples/modules/function-equations/Main.fib),
the pure [request API package](../examples/packages/request-api/src/Mail/Request.fib),
and the qualified, generic [Sum client](../examples/packages/sum-client/src/Main.fib).
For example:

~~~sh
fibril test --package examples/packages/request-api/fibril.yaml
fibril run --package examples/packages/sum-client/fibril.yaml
~~~

The request package labels values; it does not implement an HTTP server or send
email. Motive inference is convenience, not additional core expressive power.
Use an explicit `return` whenever a dependent result or inference limitation
requires it. See the [dependent example](../examples/modules/direct-data-case-dependent/Main.fib).

![Constant data-case motive inference](diagrams/data-motive-inference.svg)

## What is inferred

The direct-case frontend first checks constructor identity and coverage against
the inferred nominal scrutinee and elaborates each nullary or unary branch with
its actual field quantity and type. It asks the erased checker for each branch's
type. For a unary arm, its Pi result must not mention the payload binder; the
elaborator removes that binder with scope-aware thinning. The resulting branch
types must be **syntactically identical core terms** and each is admitted at
most 512 raw nodes. No new normalization or conversion comparison is performed
on those result types to make them agree. In particular, beta-equivalent but
syntactically different results may be rejected; an explicit motive can work.

A constant erased lambda over the actual nominal type is then proposed as the
motive. The whole assembled ordinary `NominalCase`/`VariantCase` still goes
through independent core checking. Erased inference does not authorize runtime
uses: the checker continues to reject erased-field extraction, linear drops or
duplication, and invalid branch joins. Failure to infer a motive is not proof
that no valid explicit motive exists.

This is not general dependent motive inference. A branch result mentioning its
payload, or branches with different result types indexed by the scrutinee,
requires explicit `return`. Nor does inference use the surrounding expected
result type to resolve ambiguous or syntactically different branch types.

## Syntax, budgets and evidence

The same [direct-case layout](direct-data-cases.md) is required: an indented,
aligned multiline block, at most 64 branches, and zero or one field binder per
constructor. The first arm must be nullary or a second aligned arm must be
present; a single unary pattern remains record-pattern syntax, even without
`return`. Local constructors and qualified checked direct imports retain their
usual scope and package permissions. Wider/nested patterns remain unsupported.

Pre-clone module admission reserves space for both copies of the inferred motive
and its bounded nominal domain and result. Existing checker, constructor matching,
parser, graph and expanded-core budgets continue to apply separately. Although
this new result-comparison path does not normalize its results, the existing
checker and constructor logic can perform fuel-limited reduction; these limits
are admission policies, not hard allocation, timing or memory-safety guarantees.

Tests exercise polymorphic and qualified Sum, outer linear captures, nested
cases, local and imported constructors, request tests, authored navigation and
formatter round trips. Rejections cover unequal and beta-equivalent-but-different
branch types, payload dependency, invalid coverage, erased use and linear misuse;
unit/record parsing remains distinct. Tests are sampled implementation evidence,
not a proof of soundness, totality or termination.
