# Source-ordered declaration files

## Use cases

[Named function equations](function-equations.md) now permit `greet name = ...`
after an explicit Pi signature; parameter domains and quantities come from that
signature and ordinary core checking remains independent.

Use a named typed declaration when an operation is reused or its signature is an important contract. Explicit type parameters support generic functions; dependent signatures describe results whose types depend on inputs.

Use a typed local let for a one-off intermediate value, and direct application when a new name adds no clarity. An annotation expresses an intended type; it does not bypass checking.

Status: implemented small nonrecursive program files. This is **not** a module
system, transparent global-definition environment, or full Idris layout grammar.

## Try it

```sh
./build/exec/fibril check examples/core/declarations.fib
./build/exec/fibril eval examples/core/declarations.fib
./build/exec/fibril eval examples/core/declarations-polymorphic.fib
```

[Negation](../examples/core/declarations.fib) uses familiar explicit headers:

```fib
not : (1 flag : Bool) -> Bool
not = \(1 flag : Bool) => if flag then False else True

main : Bool
main = not False
```

The [polymorphic example](../examples/core/declarations-polymorphic.fib) states a
dependent identity signature, then applies it to Bool and True. Both examples
evaluate to True through the existing reference evaluator, not a backend runtime.

For effectful [hello world](console-runner.md), main : IO Unit now uses these
same declaration rules. Ordinary helper functions may call checked prelude
functions such as putStrLn; there is no separate console-name parser.

## Framing rules

A file is still allowed to contain a single expression. A leading name followed
by : or =, or a leading numeric quantity, selects declaration framing.

- Each signature has [quantity] name : type; quantity is optional, 0, or 1.
- The next header has the same name, optional bare parameter names, then = value.
  Named parameters inherit their types and quantities from explicit Pi signatures.
- Every signature/definition header starts in column one.
- A header's name and :/=, including any equation parameters, must share a physical line.
- Remaining header-line tokens belong to its type/value expression.
- Every continuation token on a later line must be indented beyond column one,
  including closing parentheses and let/in delimiters.
- Blank lines and comments are ignored through ordinary lexing.
- Names must be unique; one signature/definition pair named main is required.
- Signatures and values can reference only earlier declarations, not themselves
  or later names. There are no mutual/recursive groups or forward declarations.

For example:

```fib
main :
  Bool
main =
  if True
    then True
    else False
```

This is a small column-one framing rule, not general indentation-sensitive
expression parsing. Tabs retain the existing one-logical-column policy.

![Declaration lowering, not transparent global definitions](diagrams/declarations.svg)

## Elaboration and quantities

[Source.Declaration](../src/Fibril/Source/Declaration.idr) parses signature/value
pairs and lowers them to existing NLet nodes ending in a reference to main:

    let (q first : firstType) = firstValue in
    let (r main : mainType) = mainValue in main

[Resolution](../src/Fibril/Source/Resolve.idr) then performs the existing
lambda/application elaboration. No new core syntax, typing axiom, admission
escape hatch, or reduction rule is introduced.

Omitted quantity is unrestricted. Explicit linear declarations must be used
exactly once in the complete program; erased declarations cannot be returned
as runtime values. Quantities of later bindings also scale their captured inputs:
an unrestricted main may not capture an earlier linear value. Use explicit
linear quantities where the existing local policy requires them.

Each declaration introduces a beta contraction during reference evaluation.
The negation example needs four steps: two bindings, one application, one
Boolean case. The entry is fixed to main; there is no entry-selection flag.

## Important opacity limitation

These are typed local-let semantics, **not transparent global definitions**.
During body checking, earlier names are abstract variables with their declared
types. Later signatures can use those names, but conversion does not unfold the
assigned values inside that checking context.

Consequently, this currently fails:

```fib
0 Bit : Type 0
Bit = Bool
main : Bit
main = True
```

True has type Bool, while Bit is abstract during main's checking. Transparent
type aliases/type functions and global delta conversion need a separately
designed definition environment. The parser does not silently inline names or
perform capture-prone textual substitution to conceal this limitation.

The next [module/import slice](modules.md) deliberately specifies imported/global
signature preservation and transparent closed conversion separately from these
local-let semantics. Header metadata, dependency discovery, checked imports and hosted
execution of module projects now exist; see [modules](modules.md).

## Budgets, diagnostics, and trust

The driver allows at most 64 declarations and uses parser depth 256 independently
for each signature/value. Checking depth is 512 and reduction fuel stays 128;
a file within the declaration limit can still exhaust another budget. The
65,536-byte loader cap is unchanged. These are not time/memory guarantees.

Framing errors use existing located Parsing diagnostics. Unbound names retain
their original source positions. The synthesized final main reference is at EOF
after its presence is verified; lowered let spans extend to EOF. Core failures
still have no invented source caret. Erased-only checking does not grant runtime
usage permission.

[Tests.Declaration](../test/src/Tests/Declaration.idr) covers ordering, name
matching, duplication, nonrecursion, quantities, opacity, framing, comments,
CRLF, missing entries/values, budgets, dependent signatures, and evaluation.
CLI tests use real files and make examples runs both program examples.

No imports, exports, namespaces, packages, general patterns, implicit inference,
recursion/termination elaboration, effects, or complete module interface exists.
This frontend extension does not resolve the quantitative/cubical metatheory.
