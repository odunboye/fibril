# 4. Data and pattern matching

[Previous](03-types-and-quantities.md) · [Contents](README.md) · [Next](05-abstraction.md)

A data declaration introduces a finite choice of constructors. This excerpt is
from [`examples/modules/function-equations/Main.fib`](../../examples/modules/function-equations/Main.fib):

```fibril
data Request : Type where
  Health : Request
  Preview : (1 subject : String) -> Request

describe : (1 prefix : String) -> (1 request : Request) -> String
describe prefix request = case request of
  Health => prefix
  Preview subject => appendString prefix subject
```

`Health` contains no payload; `Preview` carries a string. `describe` matches
both possibilities. In the first branch it returns the prefix; in the second it
uses the subject too. The linear `prefix` is consumed once in either branch.

```sh
./build/exec/fibril run --source-dir examples/modules/function-equations examples/modules/function-equations/Main.fib
```

The output is `status: ` followed by `preview: receipt` on the next line.
The first line has a trailing space because the prefix does.

## Parameterized choices

A data type can also take erased parameters. The more detailed
[`direct-data-case` example](../../examples/modules/direct-data-case/Main.fib)
defines `Sum A B`, with `Left` and `Right` alternatives. Its constructor calls
supply the type arguments explicitly, for example `Left String Bool "hello"`.
Its `case` also shows an explicit `return` motive; the simpler example above
lets Fibril infer one.

```sh
./build/exec/fibril run --source-dir examples/modules/direct-data-case examples/modules/direct-data-case/Main.fib
```

Source data is mostly non-recursive: a restricted unary-recursive family and a
one-element list shape exist, but general recursive inductives and positivity
checking do not. Recursive functions are accepted when they are structural or when
the size-change check proves them terminating (see
[function equations](../function-equations.md#general-recursion)). Direct cases support nullary and
unary alternatives, not arbitrary nested or multi-field patterns. See
[data declarations](../data.md) and [direct data cases](../direct-data-cases.md).

## Exercises

1. Change the message passed to `Preview` in a copy of the example and run it.
2. Add a nullary `Request` constructor and a corresponding `describe` branch.
3. Remove a branch and check the diagnostic; restore it before continuing.
