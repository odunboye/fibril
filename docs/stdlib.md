# Standard library: `std` package

Status: **first slice.** Pure-Fibril `Optional`, `Result` and `List`, shipped as the local
package [`stdlib/std`](../stdlib/std/fibril.yaml). It is not part of the bundled prelude:
a project opts in, so programs that do not use it pay nothing for it.

## Use cases

Model an absent value (`Optional`), a failure with a reason (`Result`), or a sequence you
traverse several times (`List`) without inventing a one-off data type each time. Choose
`Optional` when absence alone is enough, `Result` when the reason matters, and a
`Bool`/sentinel only for a genuine yes/no.

```yaml
# fibril.yaml
dependencies:
  std:
    path: ../path/to/stdlib/std
```

```fibril
module Main
import Std.List
import Std.Option

main : IO Unit
main = putStrLn (Std.Option.fromOptional String "empty"
  (Std.Option.mapOptional String String (\(s : String) => appendString s "!")
    (Std.List.first String (Std.List.Cons {String} "hello" (Std.List.Nil {String})))))
```

## Surface

| Module | Names |
| --- | --- |
| `Std.Option` | `Optional` (`Nothing`, `Just`), `fromOptional`, `mapOptional`, `isJust` |
| `Std.Result` | `Result` (`Err`, `Ok`), `fromResult`, `mapResult`, `isOk` |
| `Std.List` | `List` (`Nil`, `Cons`), `size`, `append`, `mapList`, `filterList`, `foldLeft`, `foldRight`, `reverse`, `any`, `all`, `first` |

Type arguments are explicit `(0 A : Type)` parameters, so call `Std.List.size Word items`.
Elements and tails are **unrestricted**: a list is an ordinary reusable value and may be
traversed more than once (unlike a linear list, which a traversal would consume).

## Design notes and limits

- **Names avoid the prelude.** A declaration named `map` collides with the prelude's IO
  `map` and fails with a misleading type error, so list functions are `mapList` and
  `filterList`. Treat prelude names as reserved.
- **Explicit type arguments.** Implicit `{A}` is accepted at constructors but not for the
  recursive call of a function with an implicit prefix; the library uses explicit prefixes.
- **Evaluator budgets bound input size.** Every function is structurally recursive, but the
  hosted evaluator (fuel 128 by default, at most 4096 for `fibril test`) and the native step
  and depth caps limit how long a list can be. This slice does not change those caps.
- **No Nat helpers** such as `take`/`drop`: a Nat predecessor must be consumed linearly,
  which does not fit these functions yet.
- **No Bytes or String helpers yet.** That is a separate step.

## Testing

`fibril test --package stdlib/std/fibril.yaml --fuel 4096` runs a hosted smoke suite. The
reference evaluator's 4096-fuel ceiling fits only about six checks, so the full suite is
[`stdlib/std/conformance`](../stdlib/std/conformance/src/Main.fib), compiled to C and run
natively by `tools/test_std.py` (`make std-test`): 24 checks, each printing `label: ok`.
A test mutates one expectation and requires exactly that check to report `FAILED`.
