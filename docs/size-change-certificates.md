# Abstract size-change certificates

## Status and use case

**Experimental graph checker. It admits core `Fix` terms (see [Fix admission](#fix-admission)); the other experiments on this page authorize nothing.**
`Fibril.Termination.SizeChange.produce` constructs a bounded closure for a
caller-supplied abstract call graph, and `verify` checks the resulting candidate
against the original graph. `Fibril.Termination.FirstOrder` also experiments
with extraction and a separate graph check over a small synthetic Nat/list body
representation, described below. `Fibril.Termination.GroupCalls` and
`GroupCheck` additionally extract and recheck calls from the restricted actual
Nat/Bool recursive-group representation; see the [group design](recursive-groups-design.md).
The graph algebra is also used by one real admission path:
[`Fix` admission](#fix-admission). The synthetic, group and single-shape core
experiments above remain isolated; none of them authorizes a program. Existing
structural equations continue to lower to independently checked recursors.

![Abstract size-change trust boundary](diagrams/size-change-certificates.svg)

## Fix admission

`Fibril.Core.Term.Fix` binds an unrestricted self variable around a function body.
The erased checker types the body against the declared function type under that
self, then calls `Fibril.Core.FixAdmission.admitFix`, which runs
`Fibril.Termination.Extract.extractFix` and `SizeChange.produce`. A `Fix` is
accepted only when the verdict is `GraphAccepted`; every other outcome, including
an inconclusive limit and unsupported syntax, refuses it. The term carries no
certificate, so nothing can be forged: the checker re-derives the graph each time.

Extraction is conservative. Matrices are over the function's own parameters. A
value can only be strictly smaller than a parameter when it is the tail of a
`SeqCase`, the field of a `RecCase`, or the predecessor of a `NatCase` on a value
that is already no larger than that parameter. Values built by constructors are
unknown. The extractor refuses a self reference that is not the head of a
saturated call, a call under a lambda that is not one of the leading parameters
(which includes a call inside the step of a recursor or fold), and any term form it
does not handle. A recursor or fold may be *used*, for example from an inlined
helper, as long as the recursion does not go through its step. A `Fix` may not capture a linear outer
variable, because unfolding copies its closure.

Conversion treats `Fix` as neutral and never unfolds it. Run-mode evaluation
(`Fibril.Core.Evaluation`) unfolds it only after the ordinary reducer is stuck,
and only at binder-free positions of closed terms, so an open call cannot unfold
forever. Fix-free terms evaluate exactly as before. The C emitter does not support
`Fix` and fails closed. Termination is a property of the checked graph under these
rules; it is not a mechanized proof of the extractor or the evaluator.

## Graph and certificate

Functions are numbered by position in an arity list. A call edge `f -> g` has
one row per argument of `g` and one column per argument of `f`. Each cell is:

| Cell | Supplied assertion about the callee argument relative to the caller argument |
|---|---|
| `Unknown` | No ordering established. |
| `NonIncreasing` | No larger. |
| `Decreases` | Strictly smaller. |

For example, a one-argument self-call with `[[Decreases]]` passes when its
certificate contains that edge. A self-call with `[[NonIncreasing]]` does not.
This says nothing about whether either assertion describes a real call.

A supplied certificate is a finite **set of distinct matrices**, identified by
both endpoints and cells. The checker validates endpoint/row/column shapes,
requires every direct call to be present, and checks closure under every
compatible pairwise composition. For a composed cell, it considers each
intermediate argument: a chain with an unknown relation establishes nothing;
otherwise a chain is strict if either component is strict. When several
intermediate arguments establish relations for the *same composed call*, the
strongest relation wins. Different call edges or paths remain distinct matrices:
merging alternative calls into one stronger matrix would be unsound.

Finally, every self-edge in the certificate that is idempotent under composition
must have a strict diagonal cell. A zero-argument self-cycle therefore fails.
The certificate may include extra edges, but those edges must also satisfy the
closure and cycle checks. This is the finite idempotent form of the size-change
criterion; see Lee, Jones and Ben-Amram, *The Size-Change Principle for Program
Termination* (POPL 2001).

The producer deduplicates direct calls in first-occurrence order and repeatedly
composes ordered pairs from a snapshot of the current set. New matrices enter
later rounds in both operand positions. A stable round returns the candidate
and the result of running `verify` on it; exhausting fuel or needing a 33rd
distinct matrix returns `ProductionInconclusive`, never a partial acceptance.
Malformed input returns `ProductionInvalid`. The producer and verifier share
the same composition operation and input-admission helper, so this is a
separate check of the candidate, **not an independent implementation of the
matrix algebra**.

`GraphAccepted` means only that these checks succeeded for the supplied abstract
graph and certificate. `GraphRejected` means the supplied certificate or graph
criterion failed; it does **not** prove that a program diverges. An admission
limit returns `GraphInconclusive`, never acceptance.

## Synthetic first-order body experiment

`Fibril.Termination.FirstOrder` is **not Fibril source or core**. Its deliberately
small, non-executable representation has an ordered group of functions with
Nat and `List Nat` argument sorts, and bodies made only of explicit saturated
direct calls, sequential/alternative composition, scoped value bindings, and
exhaustive Nat or list cases. The original `Definition` is shorthand for a Nat-only signature;
`TypedDefinition` supplies explicit argument sorts. Calls take locals or an
unrelated value of the appropriate sort: such a value is not an expression which
can hide a call. The checker validates call-argument and case-scrutinee sorts.
A Nat successor branch introduces its predecessor as local `0`; a list cons
branch introduces its tail as local `0` and head as local `1`, shifting existing
locals. `LetLocal` aliases an existing local and preserves its sort and
provenance; `LetOpaque` introduces an unrelated value of an explicit sort.
Both introduce local `0` only in their own body and cannot hide a call. There
are no indirect calls, function values, partial applications, computed binding
expressions, result types, effects, or quantity judgments.

`extract` traverses all bodies and branches in order and emits one matrix per
syntactic call site, including duplicate matrices. It tracks a row of relations
from each local to the caller's original arguments. Only a Nat predecessor or
list tail introduced in the corresponding successor branch can establish strict
decrease. Aliasing preserves known provenance but cannot create it; predecessors
and tails of unrelated values remain unrelated. A list head is unrelated to
*every* original argument, including the list; even a predecessor of that head
stays unrelated. Unknown values produce unknown rows. An out-of-scope local, wrong sort, target or arity mismatch is rejected.
For this experiment, Nat value and list length are the intended natural-number
measures; no known relation crosses sorts. The prototype does not prove that a
future Fibril representation or adapter preserves these measures.

`check` separately rewalks the same synthetic bodies against a proposed
ordered call-site list. It checks endpoints, arities, multiplicity and every
matrix cell; its local provenance uses root/descendant identities rather than
the producer's relation rows. `admittedArities` obtains graph arities only after
the same bounded body admission, rather than traversing an unchecked signature.
The two implementations are distinct walks, but
this is not a formal independence or soundness proof. A checked synthetic graph
can be passed to `produce` and `verify` for experiments. `verifyBody` enforces
that order for the same body values: it first checks the proposed call-site
list, obtains admitted arities, then runs `verify` on that exact graph and a
supplied closure. Body errors/exhaustion remain distinct from the graph verdict;
body checking happens before closure admission. An accepted result
still **cannot authorize a Fibril definition**: no adapter connects this
fragment to checked bodies or proves call completeness in the language.

## Comparison with Idris 2

Idris 2 already applies size-change analysis to actual Idris definitions,
including mutually recursive functions. In this repository's Idris 2 checkout,
`src/idris2/src/Core/Termination/CallGraph.idr` analyzes normalized clause
bodies, walks nested arguments, follows generated case functions and compares
arguments with caller patterns. `Core/Termination/SizeChange.idr` composes
call graphs and checks idempotent self-cycles. The worked examples in
`src/idris2/tests/idris2/total/total017/Paper.idr` include mutual recursion,
nested calls and changing argument positions. These are Idris examples, not
Fibril acceptance tests.

Idris 2's extraction depends on its own terms, contexts, pattern definitions,
normalization and case elaboration. Fibril's current core instead uses checked
recursors such as `NatRec`, `RecFold` and `SeqFold`; it has no general named
recursive-call term. Simply invoking Idris's checker on the Idris implementation
of Fibril would not check a Fibril program, and translating into Idris would
itself require a trusted correspondence. The Idris FAQ documents limitations
around fully applied calls and higher-order applications. Idris also provides
trusted assertions such as `assert_smaller` and `assert_total`; these are not
verified decrease evidence. Its tutorial explicitly cautions that the current
Idris totality checker can miss total functions and may also accept non-total
ones, so it should not be treated as an unconditional proof oracle.

Both implementations use the finite size-change criterion; this prototype
adds a bounded certificate-checking experiment and a separate synthetic body
rewalk, not an established soundness advantage. Its graph algebra is shared
between producer and verifier. Its smaller accepted fragment is not a substitute
for Idris's real-program analysis. Do not expand the synthetic grammar solely
for feature parity: the useful next design is an explicit representation and
operational semantics for Fibril recursive definitions, together with a way to
check all calls and their decrease evidence against those exact bodies. Adapt
Idris's extraction and test ideas to that representation, while keeping
coverage, positivity, quantitative use and evaluation obligations distinct.
Until then, continue using Fibril's existing checked structural recursors.

The Idris 2 source licence is in `src/idris2/LICENSE`. Copying or adapting its
implementation requires observing its redistribution conditions; studying its
algorithms alone does not add an Idris compiler dependency to Fibril.

## Trust and future integration

The [recursive groups design](recursive-groups-design.md) proposes a concrete
source goal and the additional core, usage and evaluation boundaries; it is
not implemented.

The abstract graph checker alone cannot establish that a supplied graph contains
every real call, that its edges describe actual arguments, or that a strict cell
is true. The separate group rewalk checks those claims only for its restricted
raw Nat/Bool grammar. [Fix admission](#fix-admission) ties extraction to checked
bodies for a restricted first-order grammar; to extend the criterion further, future work must tie
complete call extraction and each relation to the **exact checked recursive
bodies and their operational semantics**, account for higher-order and mutual calls, and establish suitable
well-founded orders and compatibility of the strict/non-increasing relations
across every composed argument. Recursive definitions, positivity, dependent
conversion, quantitative use, execution and backend support also need explicit
checked designs. A producer's metadata or a graph verdict cannot substitute for
those obligations.

The finite tests are sampled implementation evidence. They include exhaustive
three-relation algebra, rectangular composition orientation, alternating and
mutual descent, missing or non-closed certificates, conflicting alternative
calls, producer/verifier agreement on a small corpus, exact synthetic call-site
checking, body-bound certificates, forged decreases, mixed-sort calls,
list-head non-descent, aliases and opaque bindings, scope shifts, branch and
mutual calls, round and capacity boundaries, malformed shapes,
zero-argument cycles and admission failures. They are
not a mechanized proof of the size-change theorem, termination of Fibril terms,
whole-language soundness or compiler correctness.

## Admission

This first checker admits at most 16 functions, 8 arguments per function, 128
direct edges and 32 certificate edges. The producer admits at most 33 rounds:
each non-stable round adds a distinct edge, and one final round detects
stability. `produceWithFuel` accepts a smaller explicit round budget; exhaustion
is inconclusive. Each candidate matrix is bounded by the admitted dimensions
before it can be retained. The synthetic first-order experiment separately
admits at most 16 functions, 8 arguments per function and call, 256 aggregate
body nodes, 128 call sites, and 16 simultaneously scoped locals. Function,
argument, node and call counts are admitted before graph construction or
proposed-graph checking; the local-scope limit is checked as each successor
branch is entered. Exhaustion returns no partial graph. These are explicit
admission policies; they do not prove a hard bound on host memory, stack,
elapsed time or allocation.
