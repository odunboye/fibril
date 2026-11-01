# Primitive Unit values

Status: implemented as a small ordinary-core primitive, not general inductive
definitions or a completed quantitative unit calculus.

## Source

Unit is a reserved type name. Its constructor is the empty parenthesized value
(), including whitespace/comment-separated parentheses.

```text
let (1 value : Unit) = () in value
```

Run [the example](../examples/core/unit.fib):

```sh
./build/exec/fibril eval examples/core/unit.fib
```

    Reference evaluation: normal form (not compiled execution)
    Type: Unit
    Normal: ()

Function application also works: (\(1 x : Unit) => x) ().

## Chosen prototype rules

In a well-formed context:

    Gamma |- Unit : Type 0
    Gamma |- () : Unit

These are implemented by UnitType and UnitValue in
[Term](../src/Fibril/Core/Term.idr), with rules in
[Erased](../src/Fibril/Core/Erased.idr). UnitType is a type expression, not a
runtime value. UnitValue contributes the zero vector to runtime usage.

Scope operations leave both constructors unchanged. Both are beta normal and
head forms; structural equality distinguishes them from each other and universes.
Existing literal-universe compatibility allows Unit to check at a larger sort
in erased mode. This does not make () a type or a function.

## Quantities are not discarded

The literal uses no ambient variables. Thus a linear variable cannot silently
disappear merely because its type is Unit:

```text
\(1 x : Unit) => ()  -- rejected: x was not consumed
\(1 x : Unit) => x   -- accepted: exactly one use
\(0 x : Unit) => ()  -- accepted: erased binder
```

These choices follow the existing conservative local usage policy. There is no
special unit eta rule equating every variable of type Unit with (). In particular,
this feature does not authorize dropping arbitrary linear resources or effects.

## Deliberate limits

No dependent eliminator, pattern matching, unit eta, path constructor, or
general data declaration is added. No canonicity, quantitative preservation,
erasure correctness, or combined cubical soundness theorem is claimed.
A linear unit eliminator and cubical behavior require separate rules and review.

The ordinary unit type is background material in [HOTT13](references.md#hott13),
chapter 1; the restricted prototype rules and omissions above are our explicit
engineering choice, not an implementation of that book's complete rules.

## Tests

[Tests.Unit](../test/src/Tests/Unit.idr) covers formation, typing, zero usage,
scope operations, reduction, rejected runtime types/linear discard, source syntax,
and evaluation. Structural and erased typed generators include both constructors.
A runtime property generates closed Unit programs using checked identity and
erased beta wrappers, then checks and normalizes them to (). Sampled tests do
not establish a general canonicity or preservation theorem.
