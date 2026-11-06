# Recursive groups: proposed core boundary

## Status

**Design proposal only.** Fibril does not yet have recursive core groups, a
recursive-call core node, or general source termination checking. The existing
[structural equations](function-equations.md) lower to checked recursors. The
[size-change experiment](size-change-certificates.md) checks synthetic bodies,
not Fibril programs. Isolated experiments also check and run a tightly
restricted actual open core body under a hypothetical self variable, as described
below. None of this changes what the compiler accepts.

## A concrete goal

The following direct-style shape uses the existing fixed list shape and is now
accepted as a narrowly restricted structural equation:

~~~fibril
reverseOnto : (1 items : Data.Items.Items Nat) ->
              (1 acc : Data.Items.Items Nat) -> Data.Items.Items Nat
reverseOnto items acc = case items of
  Data.Items.Empty => acc
  Data.Items.Prepend head tail =>
    reverseOnto tail (Data.Items.Prepend head acc)
~~~

The recursive call decreases the first list while changing the linear
accumulator. Fibril accepts this shape, as well as a bounded class of checked
updates using the linear head and accumulator, by lowering it to an
independently checked function-valued `SeqFold`. Its fold result is a linear
accumulator transformer: the accumulator is supplied to that transformer, not
captured by the repeatedly invoked fold step. The runnable
[linear accumulator example](../examples/modules/linear-accumulator/Main.fib)
uses strings; the [computed-update example](../examples/modules/linear-accumulator/Decorated.fib)
transforms each head. The [String-accumulator example](../examples/modules/linear-accumulator/StringAccumulator.fib)
uses a different closed accumulator type, while the [computed-base example](../examples/modules/linear-accumulator/Matches.fib)
returns a distinct `Bool` result; an [accumulator-first example](../examples/modules/linear-accumulator/AccumulatorFirst.fib)
uses the opposite argument order. [Uniform-prefix examples](../examples/modules/linear-accumulator/UniformPrefix.fib)
show erased types and reusable functions held unchanged in recursive calls,
including the [accumulator-first version](../examples/modules/linear-accumulator/UniformPrefixFirst.fib).
Tests observe empty, singleton and multi-element inputs, including a nonempty accumulator. This is direct-style convenience, **not new
expressive power or general termination checking**. It does not use the
experimental size-change checker. Reference/native agreement is sampled
behavior, not a backend correctness proof.

For `(items, acc)`, the separate experimental graph analysis describes this
call with the following matrix, with callee rows and caller columns:

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

## Implemented experiment: extracting calls from a core body

`Fibril.Termination.CoreCalls.extract` is an experimental **producer** for a
narrow slice of actual `Term` bodies. After `checkHypothesis`, it requires two
linear `Items Nat`-shaped arguments and the same list result; two literal linear
lambdas; and a top-level `SeqCase` directly on either argument. The motive and
constructor annotations must be literal and have the same list key. Each case
branch must be either a call-free value or one saturated direct self-call whose
arguments are call-free locals or supported constructors. Everything else,
including recursive calls nested in arguments, is rejected—not silently ignored.
The 256-node and key admissions from `checkHypothesis` apply before extraction;
this particular shape has two arguments, at most two calls and fixed local scopes.

The producer uses the actual scoped case binders: in the cons body the locals
are tail, head, second argument, first argument and self. The tail gets a strict
relation to the matched argument; the head is unrelated. Constructor expressions
are unknown, even when they reconstruct the input. The nil and cons calls remain
in order. Tests extract the expected matrix from the actual reverse accumulator
body, switch the scrutinized argument, reconstruct the list and reject a
well-typed nested call.

`Fibril.Termination.CoreCheck.check` separately rewalks the same candidate using
root/descendant identities rather than the producer's relation rows. It
compares every proposed call site in order, including endpoints, matrix cells
and multiplicity, and rejects unsupported body forms, missing or extra calls,
and malformed edges. `verifyCore` first performs that rewalk and then checks
the supplied closure against that exact call list. The two walks share the
ordinary typing/usage checker, syntax definitions and assumptions, so this is
not a formal independence or soundness proof. Tests reject forged decreases,
reordered and missing calls, stale graphs and invalid closures.

Even `GraphAccepted` is **not authority to admit recursion**. There is no
recursive core representation or semantics, no proof that this restricted
walk is complete or preserves typing, and no connection to source acceptance,
ordinary evaluation, conversion or a backend.

## Isolated core-body reference experiment

`Fibril.Termination.CoreReference.evaluate` exercises this restricted actual
body without adding a recursive core construct. Every invocation reruns
`verifyCore` on the candidate and supplied calls and closure. It accepts only
two bounded, closed, canonical lists of natural numbers with the exact list
key. It applies the open body to those inputs and follows existing
`Core.Reduction.step` contractions, except that a root saturated self-call
unfolds to the same body applied to its arguments. The checked fragment admits
no nested self calls; an unexpected neutral or noncanonical final term is not
success. It returns only a canonical closed list and rechecks its ordinary type
and runtime usage.

Each ordinary contraction and self-unfold costs fuel. Zero fuel does not invoke
a speculative reduction step. Input admission, a conservative transition
node/key growth estimate before each step, a 64-character candidate key limit
and a 4,096-step maximum are separate policies; exhaustion is a failure, not a
partial result. They are not hard limits on host time, stack or allocation.
The reference strategy and ordinary checking have no proved preservation,
normalization, or equivalence theorem. Running this isolated experiment does
not expose recursion to Fibril source, ordinary conversion, the evaluator or
backends. Tests observe actual reverse order, including a nonempty accumulator,
and reject invalid inputs, stale or forged graphs and insufficient fuel.

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
   The isolated reference experiment above is an initial piece of this stage,
   not its completion: the target is the `reverseOnto` example with a checked
   recursive representation, not a hand-authored graph or precomputed result.
   Keep it isolated from dependent conversion and source acceptance until their
   contracts are implemented.
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
