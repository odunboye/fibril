# Permission joins for alternatives

Status: implemented finite permission algebra, used by ordinary Boolean
branching. It is not a proved quantitative term calculus or a cubical rule.

## Why addition is wrong

Simultaneous subterms combine through semiring addition: using a variable once
in each of two evaluated subterms yields unrestricted usage. Alternatives select
one path. Two exact-once alternatives must therefore remain exact-once.

The earlier exact-vector equality policy was too strict and not reduction-stable
under unrestricted application. [The regression](../examples/core/branch-permissions.fib)
normalizes two unrestricted observations to zero versus one. The new join permits
that discrepancy precisely when ambient permission is unrestricted.

## Permission inclusion

The local allows policy has three permissions:

- 0 admits only observed 0.
- 1 admits only observed 1.
- Unrestricted admits every observed coefficient.

The exact permissions 0 and 1 are incomparable. **0 is not a bottom permission**:
it is the identity of simultaneous addition, not of this alternative join.

![Permission inclusion; not universe subtyping](diagrams/permissions.svg)

The least common permission is:

| join | 0 | 1 | unrestricted |
| --- | --- | --- | --- |
| 0 | 0 | unrestricted | unrestricted |
| 1 | unrestricted | 1 | unrestricted |
| unrestricted | unrestricted | unrestricted | unrestricted |

[Quantity.joinQuantity](../src/Fibril/Core/Quantity.idr) implements this table.
[Usage.joinUsage](../src/Fibril/Core/Usage.idr) applies it pointwise.

## A host-checked coefficient law

The total Idris 2 proof joinAllows establishes:

    allows permission (joinQuantity left right)
      = (allows permission left && allows permission right)

The proof enumerates the finite cases and uses reflexivity; it has no postulates
or totality escape hatches. This precisely characterizes branch admissibility for
the implemented local policy. It is checked by **Idris 2**, not by Fibril.

The Boolean analyzer computes:

    conditionUsage + joinUsage thenUsage elseUsage

Ordinary binder discharge and ambient context validation then enforce permissions.
A 1/0 discrepancy requires unrestricted permission and is rejected for a linear
binder. A 1/1 pair remains linear. A possible erased extraction is rejected too.
The condition's use is additional, not one of the alternatives.

This changes observed requirements, not type compatibility: branch types still
must have equal normalized forms. There is no general branch-type least upper bound.

## Validation and remaining work

[Tests.Alternatives](../test/src/Tests/Alternatives.idr) checks every coefficient
triple for associativity, commutativity, idempotence, the permission identity,
and distribution through simultaneous addition and scaling. It also checks
pointwise vectors and positive/negative ambient resource examples.

A new Hedgehog property constructs typed programs in an unrestricted Bool/Unit
context, with differing branch observations, beta wrappers that discard inputs,
and neutral/literal conditions. It checks permissions before reduction, after
one step, and after normalization. Exact observed vectors need not be preserved;
their admissibility is the invariant being sampled.

These facts do not prove typed substitution, quantitative subject reduction,
canonicity, erasure correctness, effects/branch semantics, or cubical boundary
accounting. The prior counterexample is fixed; no general preservation theorem
is claimed, and reference evaluation still rechecks its result.
