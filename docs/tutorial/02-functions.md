# 2. Values and functions

[Previous](01-getting-started.md) · [Contents](README.md) · [Next](03-types-and-quantities.md)

A declaration has a signature and a definition. In
[`examples/core/declarations.fib`](../../examples/core/declarations.fib):

```fibril
not : (1 flag : Bool) -> Bool
not = \(1 flag : Bool) => if flag then False else True

main : Bool
main = not False
```

The signature says that `not` accepts a Boolean and returns a Boolean. The
lambda introduces the argument `flag`; the conditional chooses a result. Function
application uses spaces, so `not False` applies `not` to `False`. The `1`
marks a linear argument, discussed in the next chapter. Here `flag` is used
once, as the condition.

```sh
./build/exec/fibril eval examples/core/declarations.fib
```

The result is `True`. Definitions are source-ordered: an ordinary definition can
use earlier bindings, not itself or a later definition. Recursive definitions are
not supported. Signatures and definition headers begin in column one.

## Equations

The named equation form avoids repeating the lambda's binders. For instance,
[`examples/modules/function-equations/Main.fib`](../../examples/modules/function-equations/Main.fib)
contains:

```fibril
identity : (0 A : Type) -> (1 value : A) -> A
identity T item = item
```

The signature supplies the argument types and quantities; `T` and `item` are
local names for those arguments. This form supports one equation with an
explicit signature. Flat constructor-pattern clauses are nonrecursive and subject to case coverage and quantity checks.

```sh
./build/exec/fibril run --source-dir examples/modules/function-equations examples/modules/function-equations/Main.fib
```

See [declarations](../declarations.md), [function equations](../function-equations.md)
and [strings](../strings.md).

## Exercises

1. Copy `declarations.fib`; replace `not False` with `not True` and evaluate it.
2. Replace the branches of `not` with `True` and `False`. What changes?
3. Experiment with `appendString` in a copy of `examples/core/string-append.fib`.
