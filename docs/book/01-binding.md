# 2. Binding without accidental capture

## Learning goals

Read de Bruijn indices, explain scope-indexed syntax, and trace substitution
through a binder.

## Names versus positions

A user writes names. The core uses positions: index 0 is the newest variable,
index 1 the next older. In a two-entry context A : Type0, x : A:

- Variable FZ denotes x.
- Variable (FS FZ) denotes A.

[Term](../../src/Fibril/Core/Term.idr) uses Term n with variables Fin n.
There is no constructor for a free variable in Term 0. This prevents dangling
indices, not bad typing.

## The grammar

Universe stores a literal level. Pi and Lambda store a quantity, domain, and
body. Apply stores function and argument. Unit/Bool atoms and their case nodes
are also present; case children remain in the same scope.

A binder domain has scope n; its body has scope S n. Its own variable cannot
occur in its domain. The body may refer to it at FZ.

## Worked example: polymorphic identity

```idris
Lambda Erased (Universe 0)
  (Lambda Linear (Variable FZ) (Variable FZ))
```

The first binder introduces A. The inner domain's FZ means A. The inner body's
FZ means x, because x has now become the newest entry.

Its type is:

```idris
Pi Erased (Universe 0)
  (Pi Linear (Variable FZ) (Variable (FS FZ)))
```

The result type refers to A, now one position older.

These are excerpts of the checked [Checking example](../../examples/src/Examples/Checking.idr),
not standalone Fibril surface programs.

## Why substitution must lift

Suppose a replacement is a free variable v0. Substituting beneath a new lambda
without shifting it would turn that free variable into the lambda's bound one.

liftSubstitution therefore:

- Leaves the new FZ as Variable FZ.
- Replaces FS i with the **weakened** original replacement for i.

rename performs the corresponding index transformation. weaken inserts a newest
variable; instantiateTerm removes it by substitution. No evaluation is performed
by these functions.

## Prove that renaming behaves structurally

[Renaming laws](../renaming.md) are now total Idris 2 proofs, not just sampled
properties: identity preserves every scoped term, sequential maps compose, and
lifted renaming commutes with weakening. Pointwise map agreement is sufficient;
no function-extensionality axiom is used. Binder cases distinguish the outer
annotation scope from the extended body scope.

The results concern raw syntax, including ill-typed terms. They are checked by
Idris 2 and do not establish Fibril typing or quantitative preservation.

## Inspecting syntax

[Pretty](../../src/Fibril/Core/Pretty.idr) gives terms a shared diagnostic
representation: v0 is the newest variable, Type0 a universe, and fully
parenthesized Pi/Lam/application forms expose tree structure. It preserves
quantities and annotations without evaluating. This is debug notation, not a
surface syntax with a parser. CLI output and property counterexamples share it,
so fixes to rendering do not have to be repeated in each test generator.

## Source-reading exercise

Trace instantiateTerm through a lambda whose body references an outer variable.
Find the regression named “term replacement avoids capture” and explain why its
expected result retains FS FZ.

**Theory:** [DEBRUIJN72](../references.md#debruijn72).
**Further detail:** [core draft](../core-draft.md).
**Boundary:** all these functions manipulate syntax; none prove its type.
