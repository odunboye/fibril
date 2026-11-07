# Function pattern clauses: implementation plan

Status: a narrow first slice is implemented. Two or more contiguous clauses
with a single flat unqualified constructor pattern and at most one named field
per clause lower to checked data cases. This supports concrete instantiations of
generic sums in named modules. Constructor coverage, field usage, and types are
checked by the existing case machinery. Clause bodies cannot mention the
function's name, even when shadowed. Other arguments, nested patterns, wildcards, general binding catch-alls, qualified constructors, and mutual clauses
are not supported. Flat Nat clauses and direct Nat cases are supported when the
linear successor predecessor is consumed exactly once. A discarded explicit predecessor remains unsupported; the bounded Nat binding catch-all is described below. Ordinary single-equation behavior is unchanged.

The parser retains the final bare clause head as an authored, unresolved
`FinalBarePattern` token, including its source span. It may denote a nullary
constructor or a future binding catch-all; it is not itself a binding-site certificate. Constructor resolution remains in
force; only the bounded Nat case described below can bind an unknown head. In particular, lowercase
constructor names continue to work. Navigation does not invent a binder for an
unresolved head. The lowering also preserves constructor, payload and body spans;
the synthetic scrutinee is not exposed as a navigation binding.

Checked resolution must treat a resolved visible name as a constructor
or reject it, not silently turn a wrong constructor into a binder. Only a final
bare lowercase name with no visible global or ambiguous candidate may become a
binder; unused binders are permitted. Uppercase unknown names remain errors.
Other families and general catch-alls remain unsupported.

## Current Nat catch-all progress and limitations

A grouped equation with exactly a checked `Zero` clause followed by a bare
lowercase unresolved name can now lower to a one-step Nat case. The successor
branch binds the reconstructed `Succ` value; the predecessor is unrestricted,
so independent runtime checking rejects a linear scrutinee. Known, shadowed,
or ambiguous names still follow constructor resolution and fail closed. The
binder may be unused. Navigation still treats the authored head as unresolved
and does not link the head or its binder references. It suppresses same-spelled outer targets
in the final bare clause body, including when the head is a constructor, rather
than risk incorrect references without a checking certificate.

The public `DeclarationWithRole` constructor now takes the added `finalPattern`
field. This is an API arity change for direct constructor clients; `Declared`
and `Defined` retain their existing signatures and initialize it to `Nothing`.

## Goal and first boundary

Support grouped function equations with flat constructor patterns, including
parameterized sums, by lowering them to the existing typed case machinery.
Initially require a signature, contiguous same-name clauses, one patterned
argument, variable-only remaining arguments, exhaustive explicit constructor
coverage, and nonrecursive bodies. Reject unsupported patterns and recursion
explicitly. Preserve existing one-equation behavior.

The desired final catch-all form is a separate milestone:

```fibril
isZero : Nat -> Bool
isZero Zero = True
isZero n = False
```

A binding catch-all must preserve the entire matched value without duplicating
or silently discarding linear fields, and must respect dependent branch types.
Do not assume that expanding it into constructor cases is generally safe.

## Implementation sequence

1. Extend authored declarations with grouped clauses, pattern nodes, and original
   token spans. Parse bounded, contiguous clauses; admit one binding site for the
   function. Decide and explicitly reject clause forms in mutual/implementation
   declarations until implemented. Preserve existing declaration framing.
2. Resolve constructors using the checked scrutinee type and existing case
   elaboration. Lower exhaustive flat patterns to an equation lambda and data
   case with capture-avoiding synthetic binders. Preserve authored syntax for
   diagnostics and source tooling; never treat synthesized spans as authored.
   Use existing branch coverage and independently check the resulting core.
3. Add a final wildcard only where all expanded branches pass independent type
   and quantity checking. Specify ordered semantics and reject unreachable or
   unsupported overlap. Add binding catch-alls after their ownership and motive
   handling are established.
4. For structural recursion, normalize into exactly the existing recognized
   equation/case shape before existing admission, reservation and checking. Do
   not use a size-change graph as authority for general recursion. Handle mutual
   structural equations as a separate, limited milestone.
5. Only then consider nested or multi-column patterns, general usefulness and
   coverage, dependent refinement, and broader constructor payload shapes.

## Integration and validation

- Parser and authored AST: `Source/Declaration.idr` and
  `Source/Declaration/Syntax.idr`; preserve layout, budgets, duplicate and
  export rules.
- Matching: `Elaboration/Expression.idr` and `Elaboration/DataCase.idr`;
  recognize checked constructor identity, quantities and supported motives.
- Recursion: `Driver/ModuleCheck.idr`; preserve shape-sensitive candidate
  recognition and resource reservations.
- Source tooling: navigation, rename, symbol indexing, formatting, shape
  equality and diagnostics need original clause and binder spans.
- Tests: parser framing, generic sum coverage and imports, incorrect constructors
  and payloads, linear discard/duplication/capture, overlapping and missing
  branches, dependent motives, recursion rejection, budgets, formatting and
  navigation; compare behavior against handwritten cases on hosted/native
  execution where supported.

Existing `docs/direct-data-cases.md`, `docs/function-equations.md`, and
`docs/mutual-structural-equations.md` describe the current boundaries. The
status above records the implemented subset of this plan.
