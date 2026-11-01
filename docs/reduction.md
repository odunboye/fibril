# Ordinary reference reduction and beta comparison

Status: implemented on scoped syntax; not a typed evaluator or the final
definitional equality judgment.

## Operations

[Reduction.idr](../src/Fibril/Core/Reduction.idr) provides:

- step: one deterministic full beta/data-case step, or no step for a normal form.
- normalize: bounded repeated stepping, returning Normal or OutOfFuel.
- betaCompare: normalize both inputs and return EqualNormalForms,
  DifferentNormalForms, or Inconclusive.

The reducer uses the capture-avoiding substitution in Term.idr. It contracts a
head lambda application before inspecting its argument or annotation, otherwise
searches function before argument. In standalone Pi/Lambda terms it searches
domain before body, reducing under binders. UnitType and UnitValue are stable
atomic forms. UnitCase UnitValue body contracts to body, introducing an explicit
single-constructor computation rule but no eta rule. Other cases reduce their
scrutinee first, then their body when the scrutinee is stuck.

![Selected static calls](diagrams/calls.svg)

Boolean cases contract directly on True/False. Otherwise full reduction searches
condition, then true branch, then false branch. Weak-head exposure searches only
the condition until selecting a branch. See [Boolean rules](boolean.md).

## A proved root beta compatibility law

[Instantiation/root-beta proofs](beta-laws.md) now connect structural substitution
laws to the actual step function. Renaming/substituting a known root lambda
application yields the correspondingly mapped contractum. This is not typed
preservation or a proof for arbitrary contextual steps; unrestricted substitution
can create earlier redexes and change the selected step.

## Weak-head exposure for checking

[WeakHead.idr](../src/Fibril/Core/WeakHead.idr) adds stepHead and weakHead.
They reduce only along the function spine until the outer constructor is exposed.
They do not enter Pi/lambda domains or bodies, or neutral arguments.

A Pi can therefore be exposed at zero fuel even if its codomain contains redexes.
The result is HeadForm, not Normal: it must never be mistaken for a full normal
form. HeadLimit explicitly records exhaustion. Erased and runtime checkers now
use this service only to inspect type shape; betaCompare still fully normalizes
both sides for type comparison.

Tests include divergence on the head spine, ignored divergent bodies/arguments,
and generated compatibility with full normalization over the erased typed corpus.
These are not a confluence or typed conversion proof. Exposing outer syntax does
not skip context/domain validation, and sameSyntax is not used as conversion.

The benchmark suite includes expose-full and expose-head on identical constructed
Pi inputs; current small fixtures are overhead-sensitive and establish no general
speedup. The concrete improvement is avoiding irrelevant reductions for shape
inspection, not a measured universal performance claim.

## Proved fuel algebra

[Fuel laws](reduction-fuel.md) now prove splitting/resumption, success stability
under additional fuel, and absence of a next step in an actual successful result.
continueNormalization exposes the continuation operation as a host API. It is not
a new CLI mode; raw result tags remain diagnostic data, not certificates.

## Fuel is not a timeout

Each fuel unit permits one beta, Unit-case, or Boolean-case contraction. The reducer checks whether a step is available
even at zero fuel, so a normal input succeeds at zero and a one-step expression
succeeds with one unit.

Finding a step, substitution, syntax comparison, and term growth can be costly.
Fuel does not bound wall-clock time, allocation, stack, or output size; it is not
a sandbox or a hard-real-time mechanism.

OutOfFuel retains the unfinished term. DifferentNormalForms is returned only
when both sides reach distinct structural normal forms. If either side exhausts,
comparison is Inconclusive—even for syntactically identical divergent inputs.

## Limits and trust

- There is no eta rule, cubical computation, unfolding of definitions, or
  universe cumulativity.
- Arbitrary scope-correct terms include divergent self-application and ill-typed
  annotations. The reducer does not certify their validity.
- Beta steps preserve scope by the types of structural operations; type
  preservation and quantitative preservation have not been proved.
- Normal-form comparison treats annotations and quantities structurally. Its
  relationship to a future typed conversion judgment needs explicit rules.
- OutOfFuel must never be treated as acceptance or proof of inequality.
- No complete evaluator for the intended total language is claimed.

## Theory correspondence

[DEBRUIJN72](references.md#debruijn72) is background for substitution under
nameless binders. [ATKEY18](references.md#atkey18) motivates the separate
quantitative preservation obligations. The deterministic strategy and fuel API
are our engineering choices, not algorithms verified by those references.

## Validation

Tests in [Tests.Reduction](../test/src/Tests/Reduction.idr) cover exact/zero
budgets, reduction under binders, capture avoidance, discarded divergent
arguments, divergent inputs, and all three comparison outcomes.

Next: settle ordinary subusage and typed conversion rules before connecting
this reference service to inference. Inconclusive conversion needs a structured
checker diagnostic rather than a Boolean coercion.
