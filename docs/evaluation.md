# Checked reference evaluation

Status: implemented for the ordinary expression subset. This is **not compiled
execution**, an IO interpreter, or a C/JavaScript backend.

## Try it

```sh
./build/exec/fibril eval examples/core/evaluate-identity.fib
./build/exec/fibril eval --fuel 1 examples/core/evaluate-identity.fib
```

The [example](../examples/core/evaluate-identity.fib) applies a function identity
to another identity. Output includes:

    Reference evaluation: normal form (not compiled execution)
    Type: (Pi 1 Type0 Type0)
    Normal: (Lam 1 Type0 v0)

Output uses explicit core notation, not round-trippable surface syntax.

## Pipeline

[Driver.Evaluate](../src/Fibril/Driver/Evaluate.idr) performs:

1. Bounded strict file loading, parsing, and lexical resolution.
2. Ordinary typing and runtime usage checking through shared Driver.Check preparation.
3. Full reference beta normalization with the requested fuel.
4. Rechecking the normal form against the original inferred type.
5. Reporting only after all steps succeed.

Checking happens before reduction so optimization cannot conceal invalid resource
use. Post-reduction checking is an extra regression guard, not a general
preservation proof or a justification of quantitative/cubical rules.

PreparedRuntime is diagnostic data, not an unforgeable kernel certificate.
Driver.Evaluate obtains it through the checking function, not arbitrary construction.

Located frontend failures from eval use the same bounded
[filename/excerpt/caret diagnostics](diagnostics.md) as check. Type/resource and
reduction failures remain unlocated rather than receiving guessed spans. The
structured source-evaluation API retains error provenance without checking twice.

## Budgets and failures

Default evaluation fuel is 128. The CLI accepts decimal 0..4096 through --fuel;
already-normal functions can succeed at zero. Fuel exhaustion exits nonzero
without a Normal report.

Parsing and checking retain their independent fixed budgets (256 parsing/checking
depth, 128 reduction fuel per type operation). Raising evaluation fuel does not
raise these other budgets. All errors propagate; none admit obligations.

Fuel bounds beta/data-case contractions only. Step discovery, substitution, full annotation
normalization, and rechecking may use substantial time/memory. This is not a
sandbox, a service-level timeout, or hard-real-time execution.

Source type ascriptions elaborate to linear identity applications. They therefore
consume beta fuel and are checked before reduction, rather than being dropped as
unverified annotations. Tests confirm an ascribed identity reduces to the same
normal form.

Typed local lets likewise elaborate to lambda applications. The
[local identity](../examples/core/local-identity.fib) reduces in one beta step
and is included in make examples. No separate storage or recursive-let semantics
are introduced.

The underlying [fuel laws](reduction-fuel.md) now have total host proofs:
combined and split normalization agree, success remains stable with additional
fuel, and actual Normal results have no next reference step. These do not prove
language normalization or extend the CLI with a resume protocol.

## Current boundaries

- Only closed ordinary programs are supported: expressions or declaration files
  lowered to typed lets with a main entry.
- Runtime type expressions remain unsupported; use check --erased for type-only checking.
- There is no eval --erased mode.
- Erased arguments/types remain present during this reference computation.
  This is not a compiler erasure implementation.
- Primitive [Unit](unit.md), [Bool](boolean.md), and small source-ordered
  [declaration programs](declarations.md) are supported; no imports, recursion, effects,
  Python calls, general inductive definitions, cubical computation,
  or backend runtime are implemented by this command.

See [reference reduction](reduction.md), [runtime checking](runtime-checker.md),
and [parser](parser.md) for the actual rules.

## Tests

[Tests.Evaluate](../test/src/Tests/Evaluate.idr) covers exact fuel, normal inputs,
invalid runtime expressions, unbound names, and rejected linear discard.
CLI tests exercise real files, bounded fuel parsing, nonzero failure exits, and
explicit reference-only labeling. make examples runs the evaluation example.
