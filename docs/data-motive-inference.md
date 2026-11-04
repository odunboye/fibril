# Data-case motive inference

## Use cases

Omit `return` for supported direct data cases with a common result type:

~~~fibril
render : (1 prefix : String) -> (1 request : Request) -> String
render prefix request = case request of
  Health => prefix
  Preview subject => appendString prefix subject
~~~

An equation's declared result can also provide a **dependent** motive when the
case scrutinizes a local variable:

~~~fibril
choose : (1 choice : Select) -> Family choice
choose choice = case choice of
  First => "first"  -- Family First reduces to String
  Second => True    -- Family Second reduces to Bool
~~~

See the runnable [dependent example](../examples/modules/direct-data-case-dependent/Main.fib),
the [nested and arbitrary-scrutinee example](../examples/modules/motive-contexts/Main.fib),
the [typed-do example](../examples/modules/motive-do/Main.fib),
the pure [request API package](../examples/packages/request-api/src/Mail/Request.fib),
and the qualified, generic [Sum client](../examples/packages/sum-client/src/Main.fib).

~~~sh
fibril run --source-dir examples/modules/direct-data-case-dependent examples/modules/direct-data-case-dependent/Main.fib
fibril test --package examples/packages/request-api/fibril.yaml
~~~

The request package labels values; it does not implement an HTTP server or send
email. Motive inference is convenience, not additional core expressive power.
Explicit `return` remains the alternative when inference is inconclusive or a
particular motive is important to communicate.

![Data-case motive inference](diagrams/data-motive-inference.svg)

## Inference and checking

The direct-case frontend checks constructor identity and coverage against the
inferred nominal scrutinee and elaborates each nullary or unary branch with its
actual field quantity and type. It asks the erased checker for branch types. For
a unary arm, the inferred Pi result must not mention the payload to serve as a
constant result; scope-aware thinning removes that binder. Results may match
syntactically or by the guarded reduction described below.

Expected types are propagated from checked module signatures through typed
lambdas, annotations, supported lets, conditionals and unit cases, prefix and
infix application arguments when a literal Pi domain is available, typed-do
terminals and do-let values, and data-case branches when a bounded motive hint
is available. Named equations carry their declared results too.

The elaborator can propose an erased motive by abstracting the scrutinee from
that result. A variable uses scoped renaming; an arbitrary scrutinee uses exact
core-subterm matching, including beneath binders. It preserves a constant
candidate when an erased check confirms that candidate checks against the
expected result; otherwise it checks an exact expected-derived motive. If that
fails, it may normalize the scrutinee once with the guarded reducer and try
abstracting its normal form, again checking the entire case against the original
expected result. This preliminary check is not authorization for runtime use. The enclosing
declaration is independently checked again, including branch quantities and
runtime permissions.

This is not complete bidirectional inference: expected types are not propagated
through every construct, and function types are not reduced merely to expose a
Pi. Matching a normalized scrutinee is not general conversion-aware subterm
matching, and nested branches are not retried with the alternative hint. A
candidate that over-generalizes, a dependent payload, an unavailable or oversized
hint, and some nested cases can still require explicit `return`. Failure to
infer a motive is not proof that the program is ill-typed. [Explicit dependent
motives](direct-data-cases.md) remain available.

## Guarded conversion

Different raw constant branch-result types can now be reduced before comparison,
so a beta-redex such as `(\(0 A : Type) => A) String` can agree with `String`.
Each reduction iteration first performs short-circuit admission of at most 512
term/list nodes, checks all present beta-redex substitution estimates before
calling the existing one-step reducer, and has its own fuel limit. A conservative
510-node pre-step ceiling leaves room for non-beta case contractions. Zero fuel
does not take a step. Rejection or fuel exhaustion is **inconclusive**, not a
proof of inequality, and requests an explicit motive where needed.

Guarded reduction now admits string literals, string operations and nominal
keys with a separate 8192-character aggregate payload admission. It estimates
both the whole current payload and any beta-substituted payload before stepping,
including repeated variables beneath binders. Length is measured using the host
String implementation **before** the estimate is capped: measurement is not a
portable short-circuit work bound. Character counts are not byte counts, and the
pre-existing syntactic-equality fast path may compare payloads before admission.
These guards limit estimated term-node and character growth after measurement;
they do not establish hard allocation, timing or memory-safety bounds. Existing
checker/constructor operations retain their separate fuel and admission policies.

## Syntax and evidence

The same [direct-case layout](direct-data-cases.md) is required: an indented,
aligned multiline block, at most 64 branches, and zero or one field binder per
constructor. The first arm must be nullary or a second aligned arm must be
present; a single unary pattern remains record-pattern syntax, even without
`return`. Local constructors and qualified checked direct imports retain their
usual scope and package permissions. Wider/nested patterns remain unsupported.
Inferred results and motive domains have 512-node admissions. Arbitrary-subterm
abstraction additionally admits scrutinee/result payloads and a 262144-unit
product estimate before comparison and weakening. Module preflight reserves
motive copies and bounded expected-type weakening in lets and data arms.

Tests exercise generic and qualified Sum, constant and expected-dependent
motives, older and shadowed binders, exact-subterm round trips, propagation through
multiple expression contexts, string/key conversion, pre-substitution rejection,
explicit fallbacks, source navigation, and formatter round trips.
Rejections cover bad branches, payload dependency without usable expectation,
invalid coverage, erased use and linear misuse. These are sampled implementation
evidence, not proofs of soundness, totality, termination or resource bounds.
