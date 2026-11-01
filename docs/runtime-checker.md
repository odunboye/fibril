# Experimental ordinary runtime-usage checker

Status: implemented prototype, not a sound quantitative cubical kernel.

[Runtime.idr](../src/Fibril/Core/Runtime.idr) combines erased ordinary type checking
with a separate type-directed resource pass. It checks functions and variables,
not machine execution or compiled runtime behavior.

## Algorithm

1. Validate context formation and infer the ordinary type with inferErased.
2. Traverse computational syntax to infer usage:
   - Variable: one use at its index.
   - Lambda: analyze the body and discharge its newest binder; retain captured
     outer usage.
   - Application: infer/expose the function's Pi, combine function usage with
     argument usage scaled by the binder quantity.
   - Erased argument: use zero runtime usage. Erased inference already checked its
     complete ordinary type; it is not an unchecked hole.
3. Validate the completed vector against ambient context permissions.

Subterms do not independently have to consume every ambient linear resource:
their usages are combined before final validation.

checkRuntime additionally validates an expected type and beta-compares before
resource checking. Success returns the ordinary inferred type and usage vector.

![Selected static calls](diagrams/calls.svg)

## Local policy

- 0 binders cannot contribute runtime uses.
- 1 binders require exactly one observed use.
- Unrestricted binders permit zero, one, or many uses.
- Passing an argument to an unrestricted binder scales its entire usage to
  unrestricted. This rejects supplying a captured linear resource even if that
  particular function happens to use its input once.
- Closure capture is counted through the lambda's outer vector; duplicating
  the closure scales the resources it captures.

This is an intentionally conservative, local policy. Its full relationship to
subusage, substitution, reduction, and erasure remains a proof obligation.
[ATKEY18](references.md#atkey18) motivates the accounting but does not validate
this implementation by citation.

## Supported boundary

Universe and Pi expressions are rejected as direct computational values.
They are permitted in annotations, types, and erased arguments.
The runtime fragment has no inductives/literals/effects yet; examples use
polymorphic functions and open contexts with abstract values.

There are no cubical term rules, borrowing, recursion, partiality implementation,
backend code generation, or verified erasure. This module's name does not mean
a C/JS runtime exists.

Type/checking limits remain explicit errors; resource diagnostics identify a
bound-variable mismatch or an ambient newest-first index. Source locations and
names are not available yet.

## Tests

[Tests.Runtime](../test/src/Tests/Runtime.idr) covers polymorphic identity, exact
linear use, linear discard, erased extraction, closure capture, argument and
closure duplication, checked erased arguments, and unsupported runtime types.

The existing erased generators are not runtime generators: constant lambdas
with linear binders are intentionally acceptable erased but invalid at runtime.
[Runtime constructive properties](../test/src/Tests/RuntimeProperties.idr) now
exercise a fixed dependent open context using erased capturing lambdas and
linear identity applications. They test beta-step/normalization preservation of
usage, and reject unrestricted duplication or erased extraction. These finite
samples are not general preservation proofs or coverage of arbitrary derivations.
