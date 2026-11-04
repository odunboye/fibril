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

For a direct omitted-motive case **as the body of a signed named equation**, the
remaining declared result is also available. When the scrutinee is a local
variable, the elaborator can propose an erased motive by abstracting that
variable from the result. Scope-aware renaming handles older variables and
occurrences under binders. It preserves a constant candidate when an erased
check confirms that candidate checks against the expected result; otherwise it
proposes the expected-derived motive. This preliminary check is not authorization
for runtime use. The enclosing declaration is independently checked again,
including branch quantities and runtime permissions.

Expected types are not yet propagated through arbitrary applications, explicit
lambdas, lets or nested case branches. Arbitrary scrutinee expressions are not
abstracted. Dependent payload results, a family that cannot be recovered from
this expected-type seam, or an incorrectly generalized motive can still require
an explicit `return`. Failure to infer a motive is not proof that the program
is ill-typed. [Explicit dependent motives](direct-data-cases.md) remain available.

## Guarded conversion

Different raw constant branch-result types can now be reduced before comparison,
so a beta-redex such as `(\(0 A : Type) => A) String` can agree with `String`.
Each reduction iteration first performs short-circuit admission of at most 512
term/list nodes, checks all present beta-redex substitution estimates before
calling the existing one-step reducer, and has its own fuel limit. A conservative
510-node pre-step ceiling leaves room for non-beta case contractions. Zero fuel
does not take a step. Rejection or fuel exhaustion is **inconclusive**, not a
proof of inequality, and requests an explicit motive where needed.

The guarded reduction path deliberately excludes string literals, string
operations and nominal keys, whose payload work is not bounded by a node count.
The pre-existing syntactic-equality fast path may still compare those payloads.
There is no claim that all definitional equalities are decided, or that these
checks establish a hard allocation, time, or memory-safety bound. Existing
checker/constructor operations retain their separate fuel and admission policies.

## Syntax and evidence

The same [direct-case layout](direct-data-cases.md) is required: an indented,
aligned multiline block, at most 64 branches, and zero or one field binder per
constructor. The first arm must be nullary or a second aligned arm must be
present; a single unary pattern remains record-pattern syntax, even without
`return`. Local constructors and qualified checked direct imports retain their
usual scope and package permissions. Wider/nested patterns remain unsupported.
The inferred result and nominal domain each have a 512-node admission; module
preflight reserves the two generated motive copies.

Tests exercise generic and qualified Sum, constant and expected-dependent
motives, older and shadowed binders, guarded beta conversion and pre-substitution
rejection, explicit fallbacks, source navigation, and formatter round trips.
Rejections cover bad branches, payload dependency without usable expectation,
invalid coverage, erased use and linear misuse. These are sampled implementation
evidence, not proofs of soundness, totality, termination or resource bounds.
