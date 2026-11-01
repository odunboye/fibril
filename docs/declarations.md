# Source-ordered declaration files

Status: implemented small nonrecursive program files. This is **not** a module
system, transparent global-definition environment, or full Idris layout grammar.

## Try it

```sh
./build/exec/fibril check examples/core/declarations.fib
./build/exec/fibril eval examples/core/declarations.fib
./build/exec/fibril eval examples/core/declarations-polymorphic.fib
```

[Negation](../examples/core/declarations.fib) uses familiar explicit headers:

```text
not : (1 flag : Bool) -> Bool
not = \(1 flag : Bool) => if flag then False else True

main : Bool
main = not False
```

The [polymorphic example](../examples/core/declarations-polymorphic.fib) states a
dependent identity signature, then applies it to Bool and True. Both examples
evaluate to True through the existing reference evaluator, not a backend runtime.

For effectful [hello world](console-runner.md), a separate restricted console
profile accepts a sole main : IO Unit entry. That path does not use these typed-let
rules or enable IO helpers, opaque aliases, or arbitrary declarations.

## Framing rules

A file is still allowed to contain a single expression. A leading name followed
by : or =, or a leading numeric quantity, selects declaration framing.

- Each signature has [quantity] name : type; quantity is optional, 0, or 1.
- The next header must have exactly the same name followed by = value.
- Every signature/definition header starts in column one.
- A header's name and :/= must be on the same physical line.
- Remaining header-line tokens belong to its type/value expression.
- Every continuation token on a later line must be indented beyond column one,
  including closing parentheses and let/in delimiters.
- Blank lines and comments are ignored through ordinary lexing.
- Names must be unique; one signature/definition pair named main is required.
- Signatures and values can reference only earlier declarations, not themselves
  or later names. There are no mutual/recursive groups or forward declarations.

For example:

```text
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

```text
0 Bit : Type 0
Bit = Bool
main : Bit
main = True
```

True has type Bool, while Bit is abstract during main's checking. Transparent
type aliases/type functions and global delta conversion need a separately
designed definition environment. The parser does not silently inline names or
perform capture-prone textual substitution to conceal this limitation.

## Budgets, diagnostics, and trust

The driver allows at most 64 declarations and uses parser depth 256 independently
for each signature/value. Checking depth stays 256 and reduction fuel stays 128;
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
