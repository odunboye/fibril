# 4. Contexts and computation

## Learning goals

Trace dependent lookup, understand reference beta reduction, and distinguish
evaluation exhaustion from mathematical inequality.

## Contexts are telescopes

[Context](../../src/Fibril/Core/Context.idr) stores Empty or Extend context quantity domain.
Each domain is scoped over its preceding context. Constructors establish this
scope relationship, not that the domain is actually a type.

lookupType weakens a stored domain each time it crosses an entry—including the
variable's own binder. In A : Type0, x : A, looking up x must return A at index 1,
not index 0.

## A beta step

[Reduction](../../src/Fibril/Core/Reduction.idr) contracts:

    Apply (Lambda q domain body) argument
      -> instantiateTerm argument body

This uses the substitution from chapter 2. At a head redex it substitutes before
evaluating the argument. Otherwise it searches function before argument.
Standalone Pi/lambda annotations and bodies are reduced too.

## Why the reducer has a budget

Our syntax permits ill-typed self-application. Scope alone does not establish
termination. The host implementation therefore uses explicit fuel:

- Normal term: reduction reached beta normal form.
- OutOfFuel term: computation is unfinished.

At zero fuel, an already-normal term still succeeds. One fuel unit permits one
beta step. Step discovery and substitution can themselves be expensive; this is
not a time, stack, memory, or real-time bound.

## Three-way comparison

betaCompare normalizes both terms with separate equal-sized budgets.

| Outcome | Meaning |
| --- | --- |
| EqualNormalForms | Both normalize to the same structural syntax |
| DifferentNormalForms | Both normalize to distinct structural syntax |
| Inconclusive | At least one reduction exhausted its budget |

Identical divergent syntax can still produce Inconclusive. We deliberately do
not turn exhaustion into an accepted equality or a rejection as unequal.

## Stop when the outer shape is enough

[WeakHead](../../src/Fibril/Core/WeakHead.idr) follows only head applications.
A Pi is already exposed even if its codomain is not normal. Checkers use this
for shape inspection, then still fully compare types when equality is required.
HeadForm and Normal are different result constructors to prevent confusion.

## Exercises

- Follow an identity application through one step.
- Explain why a constant function can ignore a divergent argument here.
- Why is sameSyntax not a replacement for betaCompare?
- What additional rules would eta or cubical computation require?

**Read:** [reduction guide](../reduction.md).
**Tests:** [Tests.Reduction](../../test/src/Tests/Reduction.idr).
**Boundary:** no general normalization or typed preservation theorem is claimed.
