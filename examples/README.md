# Examples

## Runnable bootstrap project (Idris 2)

These programs use Idris 2 and the current Fibril implementation library.
They are **not source programs compiled by Fibril**. The Checking example invokes
Fibril's experimental erased checker on explicitly constructed core terms.

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
4. `src/Examples/Checking.idr`: validate a polymorphic identity with the experimental erased core checker.
5. `src/Main.idr`: executable combining the examples; failed checks exit nonzero.

The structural proof is about interval syntax. Boolean equality checks do not
constitute a proof of solver correctness or implement univalence.

## Proposed Fibril programs

`proposed/` illustrates the intended user experience, from hello world and
ordinary proofs to advanced computational univalence and application scenarios.
These files are explicitly **not executable**. The `.fib` suffix is provisional.
Do not present them as supported language features.

As Fibril becomes usable, migrate these scenarios into real compile/run and
expected-failure tests. Keep implementation status visible.
