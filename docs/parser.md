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

    expr        ::= lambda | dependentPi | application [ "->" expr ]
    lambda      ::= "\" binder "=>" expr
    dependentPi ::= binder "->" expr
    binder      ::= "(" [quantity] name ":" expr ")"
    quantity    ::= "0" | "1"
    application ::= atom { atom }
    atom        ::= name | "Type" digits | "(" expr ")"

Omitted quantity means unrestricted. Universe levels require 1..6 decimal digits.
Lambda and both arrows have the [lexer's Unicode aliases](lexer.md).
Names currently use the ASCII identifier profile.

Application associates left; arrows associate right. A -> B becomes an
unrestricted Pi with an unreferenceable underscore binder. Use parentheses to
pass lambdas/Pi expressions as arguments. Parentheses preserve source extents.
Underscore is a wildcard, never a referenceable name.

This grammar is an explicitly annotated stepping stone, not a final syntax
promise or an indentation-based declaration implementation.

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
trailing tokens, numeric bounds, EOF positions, parser exhaustion, and checking.
CLI tests check actual files and explicit erased-mode behavior.

The initial parser is total through a decreasing recursion budget. It is not an
optimized incremental parser, Unicode identifier implementation, package loader,
or a formally verified frontend. Next steps include richer source diagnostics and
a designed declaration layer, while cubical/quantitative rules remain separate
foundational work.
