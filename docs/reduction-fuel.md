# Fuel laws and resumable reference normalization

Status: total Idris 2 proofs about the actual bounded normalizer. No theorem here
asserts that arbitrary terms normalize or that a fuel budget is a timeout.

## Continuing a result

[Core.Reduction.Fuel](../src/Fibril/Core/Reduction/Fuel.idr) exposes:

    continueNormalization extra (Normal result) = Normal result
    continueNormalization extra (OutOfFuel pending) = normalize extra pending

This is a host-library API, not a new Fibril source construct or CLI resume mode.
The pending term is the exact syntax returned by the previous run. Prior
contractions need not be repeated, but step discovery at the exhaustion boundary
can be repeated; no time/allocation improvement is claimed.

![Two fuel chunks agree with a combined run](diagrams/reduction-fuel.svg)

## Proved statements

All current raw scoped terms, including ill-typed/nonterminating syntax, are covered.

| Theorem | Statement |
| --- | --- |
| normalizeSplit | normalize (first + second) term = continueNormalization second (normalize first term) |
| normalizeMore | If normalize fuel term = Normal result, then normalize (fuel + extra) term = Normal result. |
| normalizeResume | If normalize fuel term = OutOfFuel pending, then normalize (fuel + extra) term = normalize extra pending. |
| normalHasNoStep | If normalize fuel term = Normal result, then step result = Nothing. |

Zero fuel remains significant: already-normal input succeeds at zero, while
reducible input returns OutOfFuel with its current syntax. Zero additional fuel
therefore neither advances an exhausted remainder nor invalidates a success.

The last theorem concerns reference normal form (no next step), not canonical
data, well-typedness, or a final backend runtime value.

## Proof structure

Private stopped/exhausted/advanced equations expose the exact one-step cases of
normalize. The split proof inspects that step and decreases the first budget
after a contraction; it does not assume term size decreases. Syntax can grow.

Success stability and exact resumption are equality corollaries of splitting.
The no-next-step proof follows the same fuel recursion. A claimed success at
zero with an available step would equate OutOfFuel and Normal, which is impossible.

The proofs use total recursion and host equality without holes, postulates,
unsafe casts, or totality escape hatches. Checking/reduction services do not
import the proof module, and the CLI's independent checking/evaluation budgets
are unchanged.

## Raw result tags are not certificates

ReductionResult constructors remain public diagnostic data. In particular:

    continueNormalization extra (Normal arbitrarySyntax)

retains that tag without checking its payload. None of the theorems certifies a
caller-constructed tag: the successful/exhausted premises explicitly refer to an
actual normalize call. Source evaluation still checks before reduction and
rechecks afterwards. This API does not license accepting exhausted obligations.

## Tests and limits

[Tests.Fuel](../test/src/Tests/Fuel.idr) instantiates the proofs with a chain of
beta, Unit-case, and Boolean-case contractions. It covers zero fuel, exact pending
syntax, additional fuel, and a closed **ill-typed** self-application loop that
continues to exhaust. The loop is not accepted as a checked Fibril program.

A Hedgehog property independently compares combined and split runs over small
raw scoped terms and budgets, with explicit exhaustion classification. The suite
now has 24 properties / 2,400 generated cases.

These host-checked evaluator identities do not prove type/resource preservation,
normalization of the language, canonicity, confluence, erasure, compiler/backend
correctness, cubical rules, or memory/time bounds. The fuel strategy and these
proofs are our implementation choices, not metatheorems transferred from a paper.
