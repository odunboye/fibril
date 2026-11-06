# Recursive groups: proposed core boundary

## Status

**Design proposal only.** Fibril does not yet have recursive core groups, a
recursive-call core node, or general source termination checking. The existing
[structural equations](function-equations.md) lower to checked recursors. The
[size-change experiment](size-change-certificates.md) checks synthetic bodies,
not Fibril programs. A new isolated experiment checks ordinary typing of an
actual open core body under a hypothetical self variable, as described below.
None of this changes what the compiler accepts.

## A concrete goal

The following uses the existing fixed list shape, but is **proposed syntax and is
not currently accepted**:

~~~fibril
reverseOnto : (1 items : Data.Items.Items Nat) ->
              (1 acc : Data.Items.Items Nat) -> Data.Items.Items Nat
reverseOnto items acc = case items of
  Data.Items.Empty => acc
  Data.Items.Prepend head tail =>
    reverseOnto tail (Data.Items.Prepend head acc)
~~~

The recursive call decreases the first list while changing the linear
accumulator. The current equation lowering requires non-structural parameters
to be a uniform erased or unrestricted prefix, so it does not accept this
form. This is a convenience and direct-style recursion goal, **not a claim that
reversal cannot be expressed with a fold**. A later executable test should
observe element order for empty, singleton, and multi-element inputs, including
a nonempty accumulator.

For `(items, acc)`, the call's intended matrix, with callee rows and caller
columns, is:

| | caller `items` | caller `acc` |
|---|---|---|
| callee `items` (`tail`) | `Decreases` | `Unknown` |
| callee `acc` (a constructor) | `Unknown` | `Unknown` |

This is a proposed relation, not evidence: it must be derived and independently
checked from the actual executable body, with the list tail's provenance and
constructor identity established. The new accumulator is not automatically
smaller, and the list head is not smaller than its list. A graph verdict alone
cannot authorize this program.

![Proposed recursive-group checking boundary](diagrams/recursive-groups-design.svg)

## Implemented experiment: typing under hypothetical self

`Fibril.Termination.CoreCandidate` stores a closed signature `Term 0` and a
body `Term 1`, whose only possible free variable is a hypothetical unrestricted
self. Its `checkHypothesis` first admits a bounded subset of real core syntax,
requires a literal nondependent first-order function signature and lambda body,
then uses the existing `checkRuntime` against the weakened signature in that
one-variable context. Tests check the actual scoped `SeqCase`/`SeqCons` body
for the proposed reverse accumulator, including its linear arguments. They also
show that the directly looping `self x` passes this check: **typing under an
assumption is not termination checking**. No source, evaluator, conversion or
backend accepts a recursive definition because of this API.

This experiment does not authenticate recursive call sites, enforce their
saturation, verify a graph, construct a self-referential value, or evaluate the
candidate. It accepts some well-typed uses of self that a future recursion
fragment must reject. Ordinary checker failures retain their original errors,
including checking/reduction exhaustion. Shared admissions cover 256 nodes and
4,096 sequence-key characters across the signature and body, including
annotations. Measuring an already supplied string may itself cost work; these
policies are not hard time, stack or memory limits. Checking and reduction
budgets are supplied separately. The existing ordinary checker remains experimental and no new
soundness or quantitative-preservation proof follows from its use here.

## Candidate first core fragment

The smallest useful direction is a **closed, immutable group** of explicitly
signed functions with nondependent, first-order argument and result types.
Start with one self-recursive function over `Nat` and the existing fixed
`Items Nat` shape; add mutual groups only after the single-member boundary is
working. Do not broaden data positivity. No ambient variables or linear
resources may be captured by a group body. Recursive functions are not values:
only explicit saturated calls to a member of the current group are permitted.

A candidate executable representation needs, at minimum:

- An ordered finite collection of signatures and scoped bodies, with stable
  member identities and explicit quantities. A signature cannot depend on a
  recursive result or on the group being defined in this first fragment.
- An explicit call node naming a member and containing all arguments, and
  explicit exhaustive case branches with scoped binders. Names resolved by the
  source elaborator are not themselves proof of target or constructor identity.
- Ordinary local references and enough checked construction to express the
  example, including `Prepend head acc`. Calls may occur in subexpressions only
  if every such position is checked and traversed. Otherwise reject them;
  never replace an unexamined expression with an unrelated value.
- A precise relationship to existing `Term`, contexts and type/usage checkers.
  Whether the representation is an extension of `Term` or a restricted checked
  body embedded in it remains an implementation decision. A new parallel
  evaluator for an unrelated toy language is not source integration.

Unsupported forms—including recursive function values, partial applications,
higher-order callbacks, unrestricted global dependencies, recursive calls in
types, effects, arbitrary dependent signatures and unsupported data cases—must
be rejected or reported inconclusive, not silently omitted from analysis.
Eventually supporting mutual recursion requires resolving all members as one
atomic group and checking calls against the exact member signatures.

## One body, multiple independent obligations

A prospective acceptance boundary must bind every stage to the **same exact
scoped bodies, signatures, constructor identities and dependency environment**:

1. **Admit and resolve.** Bound sizes before expansion or graph construction;
   reject malformed scopes, arities, unsupported forms, unresolved or ambiguous
   targets, and stale dependencies. A cached graph, source name, unverified hash
   or serialized “checked” flag is not authority. Any change to an input that
   matters requires rechecking.
2. **Check typing, coverage and usage.** Independently validate signatures,
   result types, constructor identities and exhaustive branches. Check each
   body with recursive calls typed by their exact member signatures; account
   for every argument using its quantity, branch joins and any allowed captures.
   In the example, consuming `items`, `head`, `tail` and `acc` is a separate
   obligation from termination. The current fold usage rules do not by
   themselves establish a new recursive-call rule.
3. **Authenticate calls and relations.** Traverse every permitted expression,
   branch, constructor argument and call argument in the checked body; visit
   even syntactically unreachable branches unless separately justified. Validate
   every saturated target and preserve each call site's matrix, including
   duplicates and alternatives. A separate rewalk must validate the proposed
   calls and every cell against the same body. List tails and Nat predecessors
   can justify descent in their branches; aliases preserve provenance; other
   values are unknown unless another rule is independently justified. Compose
   only relations backed by compatible well-founded measures. Unknown indirect
   calls are rejected, not treated as no call.
4. **Check a closure certificate.** Only after body authentication, verify
   direct-edge inclusion, shapes, closure and the idempotent-cycle condition.
   `GraphRejected` is not a proof of divergence; admission or fuel exhaustion is
   inconclusive, never acceptance. Producer/checker code shares graph algebra,
   so no formal independence or correctness proof is claimed.
5. **Publish and execute only the checked artifact.** The representation used
   for execution must be exactly the one checked. If the representation or its
   dependencies are untrusted at an entry point, revalidate them there. No
   backend may assume an unverified certificate is sufficient.

This ordering does not assume that a public record or cached boolean is an
unforgeable capability. It also does not turn the synthetic `FirstOrder.Body`
into Fibril core: a complete correspondence to executable bodies is still
missing.

## Evaluation, conversion and backends

A group requires a specified unfolding rule, evaluation order and treatment of
open calls. A call must select a checked member and substitute its actual
arguments into that member's body with capture-avoiding scope; nested calls
must keep referring to the same group. One-step unfolding must not silently
run an unrestricted host-language fixpoint. Bound reduction and substitution
before expansion; exhaustion remains an explicit failure, not equality or a
successful result. Establish renaming/substitution behavior and preservation
properties, and test them rather than claiming they already hold.

In particular, termination of a restricted runtime evaluator does **not** by
itself establish termination or coherence of Fibril's full normalization and
head-reduction strategies on open, dependent terms. Core types and motives are
terms. Do not allow recursive groups to unfold in dependent conversion until
typing, coverage, usage, substitution, operational semantics and the full and
head reduction paths have a coherent checked design. A runtime-only opaque stage
would need an explicit rule preventing its use as trusted type-level
computation; it is not sufficient just to call the evaluator “runtime only”.

IO descriptions, input ownership and native execution are separate boundaries.
Until a backend implements this representation with a reviewed contract, it
must reject it. A size-change verdict proves no execution time, stack or memory
bound, no external IO termination, and no backend correctness.

## Stages and acceptance tests

1. **Core design and representation:** settle group scoping, signatures, call
   syntax, binding and a closed checked-body contract. Document the exact
   supported expression grammar and operational rules before source acceptance.
2. **Checked reference slice:** independently check actual core/group bodies,
   their types, coverage and quantities; authenticate all call sites; verify
   their certificate; and evaluate the same checked bodies under explicit fuel.
   The target is the `reverseOnto` example, not a hand-authored graph or
   precomputed result. Keep it isolated from dependent conversion and source
   acceptance until their contracts are implemented.
3. **Source and integration:** elaborate a narrowly supported source form into
   that checked representation, preserve authored diagnostics, recheck the
   finished artifact, and make unsupported source and backends fail closed.
   Decide and implement the type-level/opacity boundary before exposing it.
4. **Broaden deliberately:** mutual calls, more data families, dependent
   signatures, first-class recursive values, native emission and effects each
   require their own semantics, tests and trust analysis.

Tests must include actual ordered reverse results; wrong or shadowed
constructors; omitted, extra, duplicate and nested calls; original-input or
constructed-input fake decreases; swapped arguments; forged cells; changed
bodies or dependencies with old certificates; unsupported recursive references;
wrong types, arities and quantities; discarded or duplicated linear values;
missing branches; malformed shapes; and every relevant admission boundary.
Check zero/successor and nil/cons cases, scope shifts and exhausted evaluation.
If native support is added, compare it against the reference semantics while
retaining the explicit warning that sampled agreement is not a correctness
proof.
