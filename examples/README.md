# Examples

## Runnable bootstrap project (Idris 2)

These programs use Idris 2 and the current Fibril implementation library.
They are **not source programs compiled by Fibril**. The Checking example invokes
Fibril's experimental erased and runtime-usage checkers on explicitly constructed core terms.

From the repository root:

```sh
pack build fibril-examples
pack run fibril-examples
```

Progression:

1. `src/Examples/Basics.idr`: hello-world text and linear identity.
2. `src/Examples/Proofs.idr`: length-indexed vectors, arithmetic induction,
   and list induction. Proofs are checked by Idris 2.
3. `src/Examples/Cubical.idr`: structural proof of interval-substitution
   identity, symbolic De Morgan equality, and face constraints.
4. `src/Examples/Checking.idr`: validate a polymorphic identity with both experimental erased and runtime-usage core checkers.
5. `src/Main.idr`: executable combining the examples; failed checks exit nonzero.

The structural proof is about interval syntax. Boolean equality checks do not
constitute a proof of solver correctness or implement univalence.

## Minimal source input

`core/identity.fib` is a checked annotated-expression source example.
Run `./build/exec/fibril check examples/core/identity.fib` from the root.
Use `lex-source` instead of `check` to inspect tokens. This is not yet a full module
or compiled program. `identity-unicode.fib` checks the same expression using
λ/⇒, and `identity-type.fib` checks its dependent function type with `--erased`.
`universe-lift.fib` exercises upward literal-universe compatibility.
`evaluate-identity.fib` runs through checked reference evaluation with `fibril eval`.
`make examples` checks the four checking examples and evaluates this fifth source
example as well as running the Idris project. It also checks
`identity-annotated.fib`, which states an explicit dependent type using an ascription.
`local-identity.fib` demonstrates a typed linear let and is evaluated by
`make examples` too. `unit.fib` evaluates a checked local Unit value, the
first ordinary data primitive; this remains reference evaluation, not compiled IO.
`consume-unit.fib` explicitly eliminates a linear Unit with case/of and is also
evaluated by `make examples`. `boolean.fib` defines linear negation using a
conditional and evaluates to True. Both alternatives are checked before evaluation.
`branch-permissions.fib` retains the former branch-equality counterexample; it now
normalizes and passes post-reduction checking under unrestricted permissions.

`declarations.fib` and `declarations-polymorphic.fib` are now runnable program
files with explicit signature/definition pairs and a main entry. Both are included
in make examples. See [declaration rules and opacity limits](../docs/declarations.md).

`hello-world.fib` now runs with `fibril run` through the restricted hosted console
profile. make examples checks it without printing, then executes it. General IO,
modules, and C/JS backends remain unimplemented; see [the exact profile](../docs/console-runner.md).

`console-sequence.fib` demonstrates a flat console do block. It validates all
literal print requests before execution and is run by make examples. This is not
general monadic IO or a new core typing rule.

`string-identity.fib` uses first-class pure String values in ordinary declarations
and a linear function. make examples evaluates it to a quoted normal form; this
does not execute console printing.

`console-expressions.fib` prints results of pure closed String applications,
conditionals, and local bindings. All arguments are core-checked, reduced and
rechecked before the first output; it does not enable file-level IO helpers.

## Proposed Fibril programs

`proposed/` illustrates the intended user experience, from hello world and
ordinary proofs to advanced computational univalence and application scenarios.
These files are explicitly **not executable**. The `.fib` suffix is provisional.
Do not present them as supported language features.

As Fibril becomes usable, migrate these scenarios into real compile/run and
expected-failure tests. Keep implementation status visible.
