# Automatic indexed-case elaboration

Status: implemented bounded elaboration prototype. The core typing, conversion,
usage and termination rules are unchanged. Inferred programs are ordinary complete
`DataCase` terms checked independently by the existing core.

## Supported cases

An expected result type can supply an indexed motive automatically. Exact variable
indices are abstracted from the result under the family's erased index telescope.
For a family with one Nat index and a result in `Type 0`, a known `Zero` or
`Succ predecessor` index also permits omission of constructor arms whose normalized
result index has the opposite outer Nat constructor.

```fibril
head : (0 A : Type) -> (0 n : Nat) -> (xs : Vect A (Succ n)) -> A
head A n xs = case xs of
  Cons k value rest => value

tail : (0 A : Type) -> (0 n : Nat) -> (xs : Vect A (Succ n)) -> Vect A n
tail A n xs = case xs of
  Cons k value rest => rest
```

These examples use the unrestricted-field Vect from [indexed data](indexed-data.md).
Its `Nil` result index is `Zero`, so a nonempty input cannot select that arm.
A generic `copy : ... -> Vect A n -> Vect A n` also needs no explicit `return`
motive, but must still cover both constructors because its index is unknown.
Single-arm inferred patterns now accept up to 64 distinct field binders, including
more than two fields. Repeated `_` binders retain ordinary usage checking.

Run the [example](../examples/modules/index-refinement/Main.fib):

```sh
./build/exec/fibril run --source-dir examples/modules/index-refinement examples/modules/index-refinement/Main.fib
```

It prints `first` and `second`, each on its own line.

## Why omitted arms do not add trust

For a successor input, inference builds a type-level Nat case as its motive. At
successor indices it returns the proposed result, abstracting the predecessor
from the expected type. At zero it returns the original family at zero. The
synthetic Nil branch therefore returns `Nil`, which really has that type.

The zero-input rule is analogous: at successor indices the motive returns the
original family, and a missing successor branch reconstructs its constructor from
all its fields. Linear fields are consumed once; erased arguments remain erased.
No branch is replaced with an unchecked inhabitant of an arbitrary type. The
complete case must pass erased checking against the requested result, followed
by the ordinary runtime usage and termination checks. The native backend sees
ordinary constructors and cases.

If a proposed inferred motive fails, the previous constant-motive elaboration is
tried. An explicitly authored motive stays authoritative and retains explicit
coverage requirements. Exhausted normalization or unresolved indices never justify
omitting an arm.

## Limits

This is not general GADT unification or equality reflection. Automatic arm omission
currently handles one Nat index and outer `Zero`/`Succ` discrimination, not arbitrary
index functions, multiple-index constraints, Boolean indices or nested constructor
constraints. The caller's index expressions and constructor results are normalized
only within the existing bounded conversion budgets. General `Fix` stays opaque.

Inference is exact-occurrence abstraction, not a complete solver. It does not
rewrite all ambient hypotheses using index equalities. Some dependent programs or
cases capturing ambient linear values still need explicit motives/helpers. Usage
checks are never skipped for an impossible arm. Unsupported cases retain checked
coverage or are rejected; no runtime resource limits are raised.

The CLI tests exercise direct head/tail, inferred copy, empty vectors with linear
fields, unknown-index coverage, wrong result types, erased-index leakage and
explicit-motive compatibility. Native tests compare the example with hosted output.
