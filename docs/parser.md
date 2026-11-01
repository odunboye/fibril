# Annotated expressions: parsing, resolution, and checking

Status: implemented end-to-end **ordinary expression subset**, not full Idris-like
declarations, modules, patterns, implicit arguments, or cubical terms.

## Try a real source check

```sh
pack build fibril
./build/exec/fibril check examples/core/identity.fib
```

The [example](../examples/core/identity.fib) contains:

```text
\(0 A : Type 0) => \(1 x : A) => x
```

It prints acceptance and the inferred explicit type:

    Runtime checking: accepted
    Type: (Pi 0 Type0 (Pi 1 v0 v1))

This checks source; it does not compile or run a Fibril executable.

## Grammar

    expr        ::= ifExpr | caseExpr | letExpr | lambda | dependentPi | application [ "->" expr ]
    ifExpr      ::= "if" expr "then" expr "else" expr
    caseExpr    ::= "case" expr "of" "(" ")" "=>" expr
    letExpr     ::= "let" binder "=" expr "in" expr
    lambda      ::= "\" binder "=>" expr
    dependentPi ::= binder "->" expr
    binder      ::= "(" [quantity] name ":" expr ")"
    quantity    ::= "0" | "1"
    application ::= atom { atom }
    atom        ::= name | "Type" digits | "Unit" | "(" ")"
                  | "Bool" | "True" | "False"
                  | "(" expr ")" | "(" expr ":" expr ")"

Omitted quantity means unrestricted. Universe levels require 1..6 decimal digits.
Lambda and both arrows have the [lexer's Unicode aliases](lexer.md).
Names currently use the ASCII identifier profile.

Application associates left; arrows associate right. A -> B becomes an
unrestricted Pi with an unreferenceable underscore binder. Use parentheses to
pass lambdas/Pi expressions as arguments. Parentheses preserve source extents.
Underscore is a wildcard, never a referenceable name.

This grammar is an explicitly annotated stepping stone, not a final syntax
promise or an indentation-based declaration implementation.

## Primitive data

Unit names the first ordinary data type; () is its value. Both are source atoms,
so `(\\(1 x : Unit) => x) ()` is a checked value-level application. The empty group
now denotes a constructor rather than an absent expression. See [Unit](unit.md)
for precise typing, usage, explicit single-case elimination, and omitted
eta/dependent-eliminator rules. `case value of () => body` introduces no pattern
binders; both children resolve in the same scope. Only the () pattern is supported.

[Booleans](boolean.md) add Bool, True, False, and `if condition then yes else no`.
Branches introduce no binders. Both must resolve/type-check, and runtime branches
use a pointwise permission join: a possible branch discrepancy requires
unrestricted permission, while matching exact-once observations remain linear. Nested conditionals associate through their
explicit then/else delimiters; a conditional used as an application atom needs
parentheses, like lambdas and lets.

## Explicit type ascriptions

Parenthesized (expression : expectedType) checks against an explicit type. The
[annotated identity](../examples/core/identity-annotated.fib) states its complete
dependent function type:

```text
(\(0 A : Type 0) => \(1 x : A) => x
  : (0 A : Type 0) -> (1 x : A) -> A)
```

Resolution elaborates an ascription into an application of a linear identity:

    (term : expected)  ~~>  (lambda (1 x : expected). x) term

This uses existing domain formation, argument compatibility, and runtime usage
rules. There is no unchecked cast or new core constructor. The synthetic binder
uses its argument exactly once and captures no resources from the term itself.
Expected types are resolved in the original environment, outside that binder.

A successful ascription reports the expected type, including permitted upward
literal-universe compatibility. Quantities and Pi structure do not silently coerce.
The extra identity application is an actual beta redex in reference evaluation;
it consumes fuel. No backend optimization/erasure is implied.

A group shaped (name : type) immediately followed by -> is a dependent Pi binder.
For an ascribed expression as an anonymous arrow domain, add another pair of
parentheses: ((expression : type)) -> result. Matching-parenthesis lookahead
disambiguates these cases; it is bounded by the input, not a claimed optimized
incremental parsing strategy.

## Typed local bindings

The [local identity example](../examples/core/local-identity.fib) uses:

```text
let (1 id : (1 x : Type 0) -> Type 0) =
  \(1 x : Type 0) => x
in id
```

Local bindings require an explicit annotation and are nonrecursive. Omitted
quantity means unrestricted; 0/1 mean erased/exactly once. Annotation and value
resolve in the outer scope; only the body sees the new name. A shadowing value
may still refer to the previous outer binding with the same name.

Elaboration uses existing core syntax:

    let (q x : A) = value in body
      ~~> Apply (Lambda q A body) value

Consequently, existing typing validates the annotation/value and computes the
dependent result through substitution. Existing usage checking enforces q and
scales captured resources. Erased local type values can occur in later types,
but cannot be extracted as runtime values.

There is no let-generalization, implicit annotation inference, recursive binding,
declaration block, or new core reduction rule. Reference evaluation consumes a
beta step for a let; no compiled storage/erasure strategy is implied. Explicit in
delimits the expression; indentation is currently cosmetic.

## Separate representations and passes

1. [Lexer](../src/Fibril/Source/Lexer.idr): categories, original spelling, spans.
2. [Syntax](../src/Fibril/Source/Syntax.idr): named expression nodes with extents.
3. [Parser](../src/Fibril/Source/Parser.idr): bounded recursive descent, complete
   input consumption, positional syntax errors.
4. [Resolve](../src/Fibril/Source/Resolve.idr): names to scoped core indices.
5. [Driver.Check](../src/Fibril/Driver/Check.idr): orchestration into existing
   erased/runtime checkers, independent of the core algorithms.

Resolution uses newest-first environments. Binder domains see only the preceding
environment; bodies see the newly introduced name. Shadowing selects the nearest
binder. Anonymous arrow binders still shift older indices correctly.

No type inference is needed to resolve lexical names. Conversely, successfully
resolving an expression does not imply it is well typed.

## Checking modes and errors

- check PATH validates ordinary typing and runtime resource usage.
- check --erased PATH validates the erased ordinary fragment only; it explicitly
  does not grant permission for runtime use.

For example, Type 0 checks erased but is unsupported as a direct runtime value.
These modes expose prototype judgments; they are not a separate proof language.

Lexing, parsing, and resolution errors retain scalar positions. Core typing and
usage errors do not yet map back to exact source spans. The driver uses parser
budget 256, checking depth 256, and reduction fuel 128. Exhaustion is failure;
these budgets and the file byte limit are not time/memory guarantees.

Every expected type in the core remains checked; there is no admitted placeholder,
implicit conversion, declaration axiom, or global-name fallback.

## Tests and limitations

[Tests.Frontend](../test/src/Tests/Frontend.idr) covers quantities, Unicode aliases,
application/arrow associativity, shadowing, domain scope, wildcard references,
trailing tokens, numeric bounds, EOF positions, parser exhaustion, ascriptions,
and checking. Ascription tests cover dependent scopes, universe compatibility,
invalid expected types, quantity disagreement, and erased extraction.
[Tests.Let](../test/src/Tests/Let.idr) adds dependent local types, exact use,
erased extraction, shadowing, nonrecursion, malformed bindings, and evaluation.
CLI tests check actual files and explicit erased-mode behavior.

The initial parser is total through a decreasing recursion budget. It is not an
optimized incremental parser, Unicode identifier implementation, package loader,
or a formally verified frontend. Next steps include richer source diagnostics and
a designed declaration layer, while cubical/quantitative rules remain separate
foundational work.
