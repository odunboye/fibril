# 5. Records and interfaces

[Previous](04-data.md) · [Contents](README.md) · [Next](06-projects.md)

## Records

A choice such as `Request` contains one alternative. A record instead groups
fields that are present together. Inspect
[`Data.Message`](../../examples/modules/records/Data/Message.fib) and its caller,
[`Main`](../../examples/modules/records/Main.fib):

```sh
./build/exec/fibril run --source-dir examples/modules/records examples/modules/records/Main.fib
```

The program prints `Records!`. The module defines a message record and a
`render` function. Its caller constructs a message with `Data.Message.MkMessage`
and passes it to `Data.Message.render`. Qualified names make the source of each
imported definition explicit. Record fields can have different quantities;
accessors are only safe where the remaining fields can be discarded. See
[records](../records.md).

## Interfaces and dictionaries

An interface describes a set of operations; an implementation supplies those
operations as a checked dictionary. This makes generic code independent of one
particular operation. For example, the [constraints example](../../examples/modules/constraints/Main.fib)
uses `Algebra.concatThree` with a string dictionary:

```fibril
Algebra.concatThree String @{Instances.Text.textSemigroup} "Hello" ", " "interfaces!"
```

The explicit `@{...}` selects the dictionary, while `String` supplies the type.
Explore `Algebra.fib` and `Instances/Text.fib` alongside the caller, then run:

```sh
./build/exec/fibril run --source-dir examples/modules/constraints examples/modules/constraints/Main.fib
```

Fibril also supports bounded local and visible implementation selection, but not
recursive instance search; interface names do not prove algebraic laws. See
[interfaces](../explicit-interfaces.md) and [constraints](../constraints.md).

## Exercises

1. In a copy of the record example, change the string passed to `MkPackage`.
2. Find the method used by the string semigroup implementation. What operation
   does it provide?
3. Compare explicit `@{dictionary}` with the visible-lookup example linked from
   the [feature guide](../use-cases.md#generic-operations-why-dictionaries).
