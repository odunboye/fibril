# Ordinary core: context and checking plan

Status: broader proposed specification. An [experimental erased ordinary
checker](erased-checker.md) now implements context formation, inference/checking,
and beta-only comparison. An [ordinary runtime-usage prototype](runtime-checker.md)
also implements the local policy below; cubical checking and metatheory remain open.

See [ATKEY18 §§2.1–2.3](references.md#atkey18) for the erased/present distinction
and substitution requirements. This draft makes implementation obligations
explicit; it is not a proof that the local subusage policy is admissible.

## Context formation

Contexts are telescopes:

    empty
    Extend Gamma q A

A domain A is scoped over Gamma, not over its own binder. Formation should
require that Gamma is well formed and A checks as a type in erased mode.
The coefficient q records runtime permission; it must not prevent references
to the variable when checking types.

Context.idr enforces scope structure only; its constructors can store ill-typed
domains. Erased.checkErasedContext now validates domains in preceding contexts.

## Dependent lookup

In context [x : A, y : B(x)], index 0 denotes y and index 1 denotes x.
Looking up y returns B(x) shifted into the full two-variable scope.

Each lookup step weakens a stored domain once. Forgetting the variable's own
binder would incorrectly capture references in dependent domains.

## Proposed checking structure

Separate:

- context formation;
- inference returning a type and usage vector;
- checking against an expected type, returning usage;
- conversion in erased mode;
- final usage validation against declared context permissions.

Usage inference must be able to return zero for variables not used by a subterm.
Do not demand that every subterm consume every ambient linear variable:
validate completed scopes/derivations at their appropriate boundaries.

### Universes

Infer Type l : Type (l+1), consuming no resources. Reject Type : Type.
Literal levels are implemented. [Upward literal-universe compatibility](cumulativity-rewriting.md)
now exists separately from equality; symbolic levels and Pi covariance do not.

### Pi

Check A as a type in erased mode. Extend by x : A and check B as a type in
erased mode. If levels are i and j, infer Type (max i j). Formation consumes
zero runtime resources, irrespective of q.

### Variables

Infer the appropriately shifted stored domain. Produce mode-indexed singleton
usage; do not reject a linear variable merely because it occurs in a type.

### Lambda

Check the domain annotation as a type. Infer/check the body in the extended
context and the same mode. Discharge the newest coefficient against mode * q.
The remaining vector records capture; final surrounding checks must constrain it.

To check against an expected Pi, compare domain annotations and require binder
quantity agreement in the initial design. No implicit quantity coercions.

### Application

Infer the function and expose a Pi through justified conversion/evaluation.
Choose erased argument mode when q = 0 or the surrounding mode is erased;
otherwise use runtime mode. Check the argument against the domain.

Return the codomain with capture-avoiding argument substitution.
Combine usage as functionUsage + q * argumentUsage. Check argument types even
when the argument is erased.

### Conversion and checking

A general checking fallback infers a type and checks directional compatibility
with the expected type in erased mode. Literal universes can lift; other pairs
currently require equal beta normal forms. Structural syntax equality alone is insufficient: beta computation
must be handled. Eta, universe conversion, and quantity equality need explicit rules.

A [bounded reference beta comparison service](reduction.md) now exists.
Typed conversion and its quantity/annotation rules remain an outstanding gate. Arbitrary scoped terms can
diverge, so a total host-language evaluator cannot assume normalization merely
from scope indices. A bounded evaluator must distinguish exhaustion from
inequality and must never accept an obligation because it ran out of fuel.

## Local usage policy and limitations

validateUsage checks a complete vector against the local 0/exact-one/unrestricted
policy; erased mode requires every coefficient zero. Errors identify the
newest-first index, expected coefficient, and observed coefficient.

This helper cannot validate context domains or term types. Its unrestricted
weakening policy still needs a complete subusage specification and substitution
argument. No safety claim follows from this helper in isolation.

Cubical dimensions/restrictions remain separate. No rules here justify resource
accounting for path boundaries, composition systems, or Glue.

## Next gates

1. Settle the ordinary fragment's subusage and conversion rules.
2. Reference beta reduction/comparison is implemented with explicit exhaustion; integrate only after typed conversion rules are settled.
3. Implement inference/checking with negative tests and no admitted obligations.
4. Only then connect cubical term constructors under specified usage rules.
