# Bounded mutual structural equations

## Status and source contract

Named modules support **exactly two** workers in an explicit `mutual where`
block. This is finite equation-to-recursor sugar, not general mutual recursion
or size-change-based admission. See `examples/modules/mutual-parity/Main.fib`.

```fibril
export
mutual where
  even : (1 n : Nat) -> Bool
  even n = case n of
    Zero => True
    Succ previous => odd previous

  odd : (1 n : Nat) -> Bool
  odd n = case n of
    Zero => False
    Succ previous => even previous
```

The signature/definition pairs must align at an indented column. Each worker:

- has an unrestricted global name and exactly one explicit linear `Nat`
  parameter, with literal `Bool` result;
- matches that equation parameter directly with exactly one `Zero` arm and one
  `Succ predecessor` arm, in either order;
- returns a Bool literal at zero;
- makes exactly one saturated call to either member on the immediate predecessor
  in the successor branch.

Names must be distinct, unshadowed and referenceable. Nat constructors must be
unshadowed checked builtins; spelling alone is not authority. Parameter and
predecessor binders cannot shadow members or the recognized Nat names.
Qualification, wrappers, extra parameters, payloads, aliases, captures, effects,
dependent results, reconstructed arguments, partial calls and nested recursion
are rejected. Export applies to the entire group. Without `export`, both
members are private. Headerless checking and the flat unchecked `elaborate`
command reject groups rather than silently flattening them.

![Bounded mutual lowering](diagrams/mutual-structural-equations.svg)

## Complete translation

For ordered members `f0`, `f1`, let their base literals be `b0`, `b1`, and their
successor targets be `t0`, `t1` in `{0,1}`. Encode member zero by True and member
one by False. Define this schematic ordinary core construction:

```text
State = (1 selector : Bool) -> Bool
P = lambda (0 predecessor : Nat). State
B = lambda (1 selector : Bool). if selector then b0 else b1
S = lambda (0 predecessor : Nat).
      lambda (1 ih : State).
        lambda (1 selector : Bool).
          if selector then ih (tag t0) else ih (tag t1)
Wi = lambda (1 n : Nat). (NatRec P B S n) (tag i)
```

`src/Fibril/Elaboration/MutualNat.idr` constructs both closed `Wi` terms. There
is no hidden dispatcher global, recursive lookup, fixpoint or certificate.
Each worker embeds the complete same dispatch table, at fixed bounded cost.

### Ownership argument

The recursor consumes its Nat input. The repeated step captures no ambient
linear value. Its predecessor is erased; each exclusive Bool branch consumes
`ih` exactly once. Each selector is consumed by its Bool case. The zero branch
has no owned predecessor to discard. Both finished workers are independently
runtime/type checked; a syntactically admitted plan is not a certificate.

### Authored-equation argument

Write `K n = NatRec P B S n`. Existing beta/iota computation gives:

```text
Wi Zero = B (tag i) = bi
Wi (Succ k) = S k (K k) (tag i) = (K k) (tag ti) = Wti k
```

This is structural recursion in the existing core, even when `k` is open.
On a neutral input the Nat recursor stays stuck; no recursive delta rule unfolds
successive symbolic branches. The implementation tests all sixteen base/target
tables, checks both worker types and compares the open successor equations.
These tests support the construction argument; they are not a formal proof of
the core checkers, normalization or compiler correctness.

## Admission, checking and publication

1. Preserve one authored group item, including both members' original spans.
2. Count both names against declaration admissions; reject duplicates.
3. Validate both finite source shapes without installing assumed globals.
4. Admit signature expansion (32 nodes per signature) before elaboration and
   reserve 128 aggregate core nodes before template construction. Check actual
   generated sizes against that reservation. Exhaustion fails closed.
5. Resolve signatures only against preceding checked bindings, then verify the
   canonical Nat/Bool signature and independently check both closed workers.
6. Only then publish both ordinary member bindings and their exports together.
   A failure in an unused member still fails the whole group/module.

Bindings, symbols, imports and checked cross-member navigation retain authored
member identities; the internal Bool selector has no source symbol. Formatting
preserves group indentation and comments rather than reflowing its bodies.

## Execution and limits

The output uses existing NatRec, BoolCase, lambdas and applications. Ordinary
conversion, reference evaluation and experimental C emission handle those
constructs; there is no separate group-machine calling convention here.
The native test checks emitted/compiled execution against the reference runner.
Agreement on successful observations is sampled evidence, not a backend proof
or agreement on fuel, allocation or failure thresholds.

The separate recursive-group/SCT experiment remains unintegrated. This feature
adds convenience for a bounded class expressible by existing recursors; it
adds no general well-founded recursion, accessibility proofs or new trusted
recursive-core rule. The `reverseOnto` source example continues to use its
existing independently checked function-valued SeqFold.

## Design gate and stop conditions

The finite contract above is the complete slice. Do not silently widen it when
an authored group fails. New payloads, aliases, dependent results or nonstructural
calls need their own scoped translation and quantity/correspondence argument.
Stop if a proposed extension needs duplicated owned values, a recursive knot,
unconditional open unfolding, unavailable transport, or SCT acceptance as an
unchecked substitute for the finished core term.
