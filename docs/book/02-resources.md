# 3. Counting resources without counting type references

## Learning goals

Understand quantities, usage vectors, closure capture, and the difference
between a binder coefficient and a checking mode.

## The coefficients

[Quantity](../../src/Fibril/Core/Quantity.idr) has three values:

| Coefficient | Intended computational interpretation |
| --- | --- |
| 0 / Erased | No runtime use |
| 1 / Linear | Exactly one runtime use |
| omega / Unrestricted | Reusable or discardable |

Addition combines simultaneous uses: 1 + 1 = omega. Multiplication scales nested
requirements: omega * 1 = omega, while 0 * anything = 0.

This saturation cannot tell two uses from twenty. It retains what this policy
needs: zero, exactly one, or potentially many.

## Modes are not quantities on binders

[Usage](../../src/Fibril/Core/Usage.idr) distinguishes ErasedMode from RuntimeMode.
An erased judgment inspects information without consuming it at runtime.
RuntimeMode contributes coefficient 1. There is no omega judgment mode.

Types may refer to a linear value without consuming it. Otherwise dependent
types would conflict with the very resources they describe.

## Worked example: an open context

Let A : Type0 be erased and x : A be linear. Newest-first runtime usage of x is:

    [1, 0]

The first entry consumes x; the second does not consume A. In erased mode both
entries are zero.

For an application with binder q, the accounting formula is:

    function usage + q * argument usage

Passing x to an unrestricted binder therefore requires omega uses of x and
fails the exact-once permission—even if that function's current body uses it once.

## Closures carry resource requirements

A lambda can capture x. Its body vector records the capture; discharging the
lambda's own binder does not discard the outer vector. Duplicating that closure
must scale its captured resources too.

The local helper allows enforces 0/exact-one/unrestricted acceptance. It is not
a complete subusage calculus. The soundness of these rules together with reduction,
erasure, and cubical features is still an obligation.

## Exercises

- Compute [1, 0] + [1, 0].
- Why must subterms not each be required to consume every ambient linear variable?
- Why does exact use not itself guarantee that a hardware handle is closed?

**Theory:** [ATKEY18](../references.md#atkey18), especially §2.1;
[MCBRIDE16](../references.md#mcbride16).
**Tests:** [runtime regressions](../../test/src/Tests/Runtime.idr).
