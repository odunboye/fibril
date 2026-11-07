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

The signature/definition pairs must align at an indented column. In the original
no-payload mode, each worker:

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
Qualification, wrappers, extra parameters beyond the payload mode below,
captures, effects, dependent results, reconstructed arguments, partial calls and
nested recursion are rejected. Aliases and argument reordering are supported
only in the separate one-alias mode described below. Export applies to the entire group. Without `export`, both
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

## Unchanged linear Bool payload

Both workers may instead have the exact signature
`(1 n : Nat) -> (1 payload : Bool) -> Bool`. A group cannot mix the two modes.
The [payload example](../examples/modules/mutual-parity/Payload.fib) alternates
an identity base and a negating base. Each successor must pass the immediate
predecessor and **the same payload variable**, in that order.

The zero arm is exactly one of:

- the payload variable;
- `if payload then <Bool literal> else <Bool literal>`.

A bare literal would discard the linear payload and is rejected. Equal literal
branches are allowed: evaluating the condition consumes the payload. Changed,
reconstructed, discarded or duplicated payloads, arbitrary base expressions,
erased/unrestricted payload parameters and argument reordering between two
structural workers are rejected.
Signature and equation binders are separate scopes and may have different
names, but binders within each scope must be distinct; the predecessor may not
shadow either equation argument or a member.

The complete extension to the construction above is:

```text
E(KeepPayload, p) = p
E(TruthTable a b, p) = if p then a else b
State = (1 selector : Bool) -> (1 payload : Bool) -> Bool
P = lambda (0 predecessor : Nat). State
B = lambda (1 selector : Bool). lambda (1 p : Bool).
      if selector then E(base0,p) else E(base1,p)
S = lambda (0 predecessor : Nat). lambda (1 ih : State).
      lambda (1 selector : Bool). lambda (1 p : Bool).
        if selector then ih (tag t0) p else ih (tag t1) p
Wi = lambda (1 n : Nat). lambda (1 p : Bool).
       ((NatRec P B S n) (tag i)) p
```

Identity remains a distinct base plan: replacing `p` with `if p then True else
False` would not preserve its open definitional equation because the core has
no Bool eta rule. Each base consumes `p` once. Each successor alternative
consumes `ih` and its own payload once, and alternatives join their usages.
The repeated step references no outer payload; only the function returned by
the fold receives the caller's owned payload.

For neutral `k` and `p`, existing beta/iota rules give:

```text
Wi Zero p = E(basei,p)
Wi (Succ k) p = K k (tag ti) p = Wti k p
```

Core tests cover all **100** syntactic base/target plans (five bases per member,
two targets per member), including open base and successor equations and both
finished worker types. CLI tests cover all 64 conditional-base tables with both
entries and both Bool values; the example additionally covers direct identity.
No new core rule or evaluator is involved.

## One forwarding alias and one structural worker

A third, separate group mode supports **one acyclic forwarding alias** and
**one structural payload worker**. Either member may come first, and each
member independently chooses the literal signature order `Nat, Bool` or
`Bool, Nat`, with both parameters linear and result Bool. See the
[reordered example](../examples/modules/mutual-parity/Reordered.fib):

```fibril
mutual where
  first : (1 n : Nat) -> (1 flag : Bool) -> Bool
  first n flag = second flag n

  second : (1 flag : Bool) -> (1 n : Nat) -> Bool
  second flag n = case n of
    Zero => flag
    Succ previous => first previous flag
```

The alias must make exactly one saturated call to the **other** member, using
its own Nat and Bool variables in the target's signature order. The worker
cases directly on its Nat argument, has one of the five payload bases above,
and calls itself or the alias on the immediate predecessor with unchanged
payload. Alias self-calls, two aliases, alias cycles, partial calls, changed or
duplicated arguments, arbitrary wrappers, captures and unsupported signatures
are rejected. Two structural Bool-first workers are **not** admitted by this
alternative. The existing two-worker modes keep their previous restrictions.

### Alias elimination and complete core construction

Eliminate the acyclic forwarding equation before constructing the core. A
worker successor call through the alias then becomes a direct structural step.
Both published entries use the **same** one-worker fold, not two distinct
selector tags (which need not convert on a neutral Nat).

```text
State = (1 p : Bool) -> Bool
P = lambda (0 k : Nat). State
B = lambda (1 p : Bool). E(base,p)
S = lambda (0 k : Nat). lambda (1 ih : State). ih
C n = NatRec P B S n
Nat-first entry  = lambda (1 n : Nat). C n
Bool-first entry = lambda (1 p : Bool). lambda (1 n : Nat). C n p
```

`forwardWorker` constructs these closed templates directly: no assumed member
references, recursive knot, runtime group evaluator or SCT acceptance.
The repeated step captures no owned argument and consumes its induction result
once; its predecessor is erased. The base consumes the payload exactly as
authored. Each finished function consumes its Nat and Bool once in either
calling order. In particular, the implementation does **not** replace the
function with its base and silently discard the linear Nat.

For neutral Nat `k` and Bool `p`, write `argsX(k,p)` for X's declared order.
Existing beta/iota rules establish:

```text
Alias(argsAlias(k,p)) = C k p = Worker(argsWorker(k,p))
Worker(argsWorker(Zero,p)) = E(base,p)
Worker(argsWorker(Succ k,p)) = C k p = Target(argsTarget(k,p))
```

`Target` can be the alias or the worker. No Bool/function eta or new open
unfolding rule is required. Tests cover all **80 plans** (five bases, two member
placements, two orders/member and two successor targets), checking core types,
open equations and source execution. The largest directly constructed entry is
26 nodes; both entries plus signatures occupy at most **62** nodes, asserted
in core tests and covered by the unchanged 128-node reservation.

Authored navigation retains both calls and their source targets even though
the core entries share a canonical implementation. An alias call navigates to
the worker; a successor call navigates to its authored target, not a hidden fold.
Imports, exports, formatting and whole-group atomic failure use the same paths
as the two structural-worker modes.

## Admission, checking and publication

1. Preserve one authored group item, including both members' original spans.
2. Count both names against declaration admissions; reject duplicates.
3. Validate both finite source shapes without installing assumed globals.
4. Admit signature expansion (32 nodes per signature) before elaboration and
   reserve 128 aggregate core nodes before template construction. Check actual
   generated sizes against that reservation. The largest payload template is
   55 nodes per worker plus five per signature, 120 aggregate; identity bases
   are smaller. Core tests assert this count. Exhaustion fails closed.
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
an authored group fails. Further payload types, more general alias graphs,
dependent results or nonstructural calls need their own scoped translation and
quantity/correspondence argument.
Stop if a proposed extension needs duplicated owned values, a recursive knot,
unconditional open unfolding, unavailable transport, or SCT acceptance as an
unchecked substitute for the finished core term.
