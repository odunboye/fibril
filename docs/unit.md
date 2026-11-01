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

## Explicit case elimination

```text
\(1 x : Unit) => case x of () => ()
```

Unlike silent discard, this explicitly consumes x. UnitCase scrutinee body adds
no binder: both children resolve in the original scope.

Chosen typing and runtime accounting:

    infer scrutinee = Unit
    infer body = B
    -------------------------
    infer (case scrutinee of () => body) = B

    usage(case scrutinee of () => body) = usage(scrutinee) + usage(body)

Erased inference checks both children and requires the scrutinee type to be
compatible with Unit. Runtime checking counts the scrutinee and body once each.
A linear scrutinee cannot also be extracted in the body; an erased input cannot
be scrutinized at runtime. The body may have any well-formed inferred type.

The new computation rule is:

    case () of () => body  -->  body

This contraction consumes one unit of reduction fuel. Full reduction first
reduces the scrutinee, then normalizes the body of a stuck case. Weak-head
reduction only inspects the scrutinee until the case contracts. No unit eta
identifies a neutral variable with (), and no general multi-branch usage rule
is inferred from this single-case rule.

Run [consume-unit.fib](../examples/core/consume-unit.fib) for an application that
needs one beta contraction and one case contraction to return (). This is pure
reference normalization, not an IO sequencing or erased backend specification.

## Deliberate limits

The only case pattern is (). No dependent eliminator/motive, general pattern
matching, unit eta, path constructor, or general data declaration is added. No canonicity, quantitative preservation,
erasure correctness, or combined cubical soundness theorem is claimed.
Cubical behavior and extensions to other data types require separate rules
and review. The explicit single-case rule below is a local prototype design.

The ordinary unit type is background material in [HOTT13](references.md#hott13),
chapter 1; the restricted prototype rules and omissions above are our explicit
engineering choice, not an implementation of that book's complete rules.

## Tests

[Tests.Unit](../test/src/Tests/Unit.idr) covers formation, typing, zero usage,
scope operations, reduction, rejected runtime types/linear discard, source syntax,
and evaluation. Structural and erased typed generators include both constructors.
A runtime property generates closed Unit programs using identity, erased beta wrappers, and case elimination,
then checks and normalizes them to (). [Tests.UnitCase](../test/src/Tests/UnitCase.idr)
covers exact fuel, constructor computation, neutral cases, type-level conversion,
rejected scrutinees, and resource failures. Sampled tests do
not establish a general canonicity or preservation theorem.
