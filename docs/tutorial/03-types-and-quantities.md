# 3. Types and quantities

[Previous](02-functions.md) · [Contents](README.md) · [Next](04-data.md)

Fibril functions can take types as arguments. This program is
[`examples/core/declarations-polymorphic.fib`](../../examples/core/declarations-polymorphic.fib):

```fibril
id : (0 A : Type 0) -> (1 x : A) -> A
id = \(0 A : Type 0) => \(1 x : A) => x

main : Bool
main = id Bool True
```

`A` is a type argument, and the type of `x` depends on it. Applying `id` to
`Bool` gives a function from `Bool` to `Bool`; applying that to `True` yields
`True`. `Type` is shorthand for `Type 0`; higher universe levels are written
explicitly. Run:

```sh
./build/exec/fibril eval examples/core/declarations-polymorphic.fib
```

## Resource permissions

The number before a binder controls how it may be used:

- `0`: erased, available for checking but not runtime computation. `A` is such
  an argument above.
- `1`: linear, used exactly once at runtime. `x` is returned once.
- No quantity: unrestricted permission, allowing the argument to be dropped or
  reused where the checker permits it.

For a conditional, a linear value cannot be consumed in only one branch and
silently dropped in the other. The checker accounts for branch usage; this is a
prototype resource discipline, not yet a file or socket ownership library.
See [runtime checking](../runtime-checker.md) and [branching](../boolean.md).

Some declarations can use implicit erased arguments, but inference is bounded;
explicit arguments remain useful when information is ambiguous. See
[implicit arguments](../implicit-arguments.md).

## Exercises

1. Evaluate the example and identify both applications in `id Bool True`.
2. In a copy, replace the body `x` with `True`. Check the result: why can this
   not implement the signature for every `A`?
3. Read `examples/core/branch-permissions.fib` and identify how branches use
   their inputs.
