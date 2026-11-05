# Structural recursion over Nat

## Use case and scope

**Implemented first recursion slice:** the reference evaluator supports a
built-in natural-number type and a dependent structural recursor. This is useful
for bounded counts, repetition and induction over natural numbers without an
unrestricted fixpoint. For example:

~~~fibril
repeat : (1 count : Nat) -> (1 text : String) -> String
repeat count text = natRec
  (\(0 k : Nat) => String)
  text
  (\(0 k : Nat) => \(1 result : String) => appendString result "!")
  count

main : IO Unit
main = putStrLn (repeat (Succ (Succ Zero)) "receipt")
~~~

The [runnable example](../examples/modules/nat-recursion/Main.fib) uses three
successors and prints `receipt!!!`. `Nat`, `Zero`, `Succ` and `natRec` are
primitive checked globals; there is no numeric-literal syntax in this slice.

This is **not yet general recursive function syntax**: self-referential
equations still fail. Nor does it implement user-defined recursive data,
recursive lists, positivity checking, mutual recursion or a termination checker
for arbitrary definitions. `natRec` gives the step an erased predecessor and a
runtime recursive result. `natRecWith` additionally allows the step to inspect
the predecessor, at the cost of requiring an unrestricted count. Explicit
structural recursion through other user types requires later work. The
experimental C backend currently rejects Nat computation; use `fibril run`.

![Structural recursion boundary](diagrams/nat-recursion.svg)

## Rule and computation

The source primitive `natRec` accepts a small-type motive, a base, an unrestricted
step and a linear count. The core rule is universe-aware:

~~~text
P : (0 n : Nat) -> Type j
base : P Zero
step : (0 k : Nat) -> (1 previous : P k) -> P (Succ k)
n : Nat
-------------------------------------------------------
NatRec P base step n : P n
~~~

Its core computation rules are:

~~~text
NatRec P base step Zero     --> base
NatRec P base step (Succ k) --> step k (NatRec P base step k)
~~~

The source `natRec` interface currently exposes motives into `Type 0`; the core
checker handles the rule above at other literal universe levels. Results may
actually depend on the input index, for example an indexed finite data value at
`Mark n`. The resulting core term is independently checked. The predecessor is
available to the type checker, but erased at runtime; the induction result is
linear and must be consumed once. The step is unrestricted because it can run
zero or many times. Consequently it cannot capture an ambient linear resource.
The base and count are each accounted for once. These are conservative usage
rules, not a proved quantitative preservation theorem.

### Inspecting the predecessor

Use `natRecWith` when the step needs the predecessor at runtime:

~~~fibril
triangle : (count : Nat) -> Nat
triangle count = natRecWith (\(0 k : Nat) => Nat) Zero
  (\(k : Nat) => \(1 previous : Nat) => add k previous) count
~~~

The complete [triangle example](../examples/modules/nat-predecessor/Main.fib)
uses `add` and prints three marks for the sum `0 + 1 + 2`. This is a separate
core recursor with step `(k : Nat) -> (1 previous : P k) -> P (Succ k)`.
The count must be unrestricted: a successor contraction supplies its
predecessor both to the step and to the recursive call. The checker scales the
count and step usage by unrestricted permission, rejecting linear captures;
the base is still used once. There is no implicit conversion between an erased
and an unrestricted predecessor binder. These are conservative rules, not a
proof of quantitative preservation.

No source annotation certifies termination: recursion in this slice is the core
recursor's structurally smaller operand. Evaluator/conversion fuel is an
operational admission and can be exhausted; it is not a termination proof or a
time, stack or allocation guarantee. Guarded speculative conversion accounts
for the next successor contraction before building it. Existing independent
checker and full reduction limits continue to apply.

## Evidence and next steps

Tests cover zero and successor computation, runtime predecessor access with an
unrestricted count, an index-dependent result, invalid steps even on `Zero`,
erased predecessor misuse, linear capture, inference for
Nat values and fail-closed native emission. Structural renaming and substitution
proofs cover the new nodes. These tests do not prove normalization, positivity,
whole-language soundness or backend correctness. Next: checked recursive
declaration representation and positivity, followed by source equation
termination checking that elaborates to checked recursors; neither is implied by
this primitive.
