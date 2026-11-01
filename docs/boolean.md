# Primitive Booleans and conservative branching

Status: implemented ordinary prototype. These values are **not interval
dimensions**, face formulas, or a combined quantitative/cubical calculus.

## Try it

```sh
./build/exec/fibril eval examples/core/boolean.fib
```

[The program](../examples/core/boolean.fib) defines and applies a local linear
negation function:

```text
let (1 not : (1 flag : Bool) -> Bool) =
  \(1 flag : Bool) => if flag then False else True
in not False
```

Output includes Type: Bool and Normal: True. This is reference normalization,
not compiled native/web execution.

## Chosen typing rules

BoolType : Universe 0. BoolTrue and BoolFalse both have type BoolType.
The source keywords are Bool, True, False, if, then, and else.

BoolCase condition yes no has no binders. Erased inference:

1. Checks the condition against Bool.
2. Infers both branch types.
3. Requires **equal normal forms**, with explicit exhaustion.
4. Returns the first branch's inferred type.

There is no implicit universe maximum, directional branch coercion, or Pi
subtyping. Use explicit ascriptions when a common larger universe is intended.
Both branches must resolve and type-check even when the condition is a literal.

A conditional can compute a type in erased mode, for example:

    if True then Bool else Unit

Both branches have type Type0; conversion reduces this expression to Bool.
This does not introduce a dependent elimination motive or branch-local equality
assumptions. Runtime type expressions themselves remain unsupported.

## Runtime resource rule

The constructors use no variables. The condition is evaluated once. Alternatives
must have exactly identical observed usage vectors:

    usage(yes) = usage(no) = shared
    usage(if condition then yes else no) = usage(condition) + shared

Do **not** add the two branch vectors: alternatives are not both executed.
For example:

```text
\(1 flag : Bool) => \(1 x : Unit) => if flag then x else x
```

uses flag once and x once, not x twice. Conversely, if one branch ignores x,
checking rejects the program. A runtime condition cannot extract an erased flag.
A linear flag used as both condition and branch result is also rejected.

Exact vector equality is intentionally conservative, including for unrestricted
ambient variables: a zero-versus-one branch discrepancy is rejected even if both
uses would separately satisfy unrestricted permission. We do not implement a
general subusage join or claim this policy is the final QTT branching rule.
The selected branch is checked before normalization can erase an invalid
alternative.

### Known reduction-stability gap

Exact observed-vector equality is not preserved by every beta contraction in
the existing unrestricted application policy. For example:

```text
\(flag : Bool) => \(x : Unit) =>
  if flag
    then (\(ignored : Unit) => ()) x
    else (\(y : Unit) => y) x
```

Before normalization both branches count x as unrestricted because application
scales its argument by the binder's unrestricted quantity. Afterwards the
branches use x zero times and once respectively. The original checks, but the
normal form fails this strict branch-equality policy.

The reference evaluation driver reports a post-reduction checking failure rather
than returning that normal form as accepted. Tests explicitly retain this
counterexample. This is a known limitation, not merely an unproved theorem:
a future branch-permission/join design must resolve it before claiming
quantitative subject reduction or relying on unchecked backend preservation.

## Computation and fuel

    if True then yes else no   --> yes
    if False then yes else no  --> no

Each contraction costs one reduction-fuel unit. Full reduction contracts a
literal condition immediately; otherwise it searches condition, then yes, then
no, including branches of neutral conditionals. Weak-head reduction searches
only the condition until selection. Unselected branches need not normalize,
but both were already type/resource checked by the evaluation driver.

Reference beta comparison now includes Unit and Boolean case computation.
No eta, equality reflection, cubical conversion, or deadline guarantee is added.

## Boundaries and tests

No dependent motives, general data declarations/pattern matrices, effects,
backend erasure, or quantitative preservation/canonicity theorem is provided.
The ordinary Boolean idea is background in [HOTT13](references.md#hott13);
the restricted checking/resource policy above is an explicit local design.

[Tests.Boolean](../test/src/Tests/Boolean.idr) covers constructors, both branches,
nesting, exact fuel, invalid conditions/branches, computational types, branch type
equality exhaustion, and positive/negative resource accounting.
Scoped/erased/runtime generators include conditionals; open runtime recipes
construct different branch syntax with matching type and capture.
These are sampled regressions, not a general metatheoretic proof.
