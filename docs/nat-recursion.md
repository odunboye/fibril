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
primitive checked globals. A decimal [numeric literal](#numeric-literals) such as `3` is
shorthand for the same Nat value.

## Numeric literals

A decimal literal such as `3` is an expression of type `Nat`, equal to `Succ (Succ (Succ Zero))`.
It is a single token, so it avoids the parser's nesting limit that long chains of `Succ` hit.
It always denotes the built-in `Nat`, so a user binding of `Zero` or `Succ` cannot change it.

- Digits only, no leading zeros (`007` is rejected; `0` is fine), and at most **256**. A literal
  stands for that many successors in the core, so the bound follows the runtimes' practical
  limits; a larger value is a parse error rather than a surprising budget failure later.
- Literals are expressions, not patterns: write `case n of Zero => ...; Succ p => ...`, not `0 =>`.
- They work anywhere a `Nat` does, including as an argument (`marks 3`) and in test suites.
  The hosted evaluator and `test` still need enough fuel for what the program computes
  (`run --fuel`, `test --fuel`); a large literal does not make a computation cheaper.
- The formatter keeps the authored spelling.

This recursor is not general recursive function syntax. A narrowly restricted
[named Nat equation](function-equations.md#structural-nat-equations) lowers to
it; other self-referential equations are checked as
[general recursion](function-equations.md#general-recursion) when a size-change
decrease exists, and fail otherwise. A separate
[unary recursive-data slice](data.md#unary-recursive-declarations) admits one
terminal and one direct linear self field, alongside a restricted parameterized
list shape. General positivity checking and mutual recursion beyond the bounded
Nat/Bool pairs remain future work. `natRec` gives the step an erased predecessor and a
runtime recursive result. `natRecWith` additionally allows the step to inspect
the predecessor, at the cost of requiring an unrestricted count. General
structural recursion through other user types requires later work. The
experimental C backend also supports these checked Nat forms, with its own
admission limits; `fibril run` remains the reference alternative.

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
recursor's structurally smaller operand. The accepted narrow Nat-equation form
constructs that same checked recursor rather than introducing a fixpoint. Evaluator/conversion fuel is an
operational admission and can be exhausted; it is not a termination proof or a
time, stack or allocation guarantee. Guarded speculative conversion accounts
for the next successor contraction before building it. Existing independent
checker and full reduction limits continue to apply.

## Evidence and next steps

Tests cover zero and successor computation, runtime predecessor access with an
unrestricted count, an index-dependent result, invalid steps even on `Zero`,
erased predecessor misuse, linear capture, inference for
Nat values, sampled native/reference agreement and fail-closed unsupported native forms. Structural renaming and substitution
proofs cover the new nodes. These tests do not prove normalization, positivity,
whole-language soundness or backend correctness. Source equation termination
was later added through a core `Fix` admitted by a size-change check, not by
elaborating to recursors; general recursive data and positivity remain future work.
