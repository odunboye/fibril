# Quantitative cubical rules: proposed general-path contract

Status: **proposed rules and execution gates**, not an implemented calculus,
completed metatheory, or authorization to broaden ordinary conversion.
The [closed Boolean experiment](cubical-alignment.md) remains a regression
baseline. The next target is general **open logical paths**, followed by a
partial, explicitly checked executable-realization interface. This document
supersedes the older roadmap's closed-only description of the next milestone.

## 1. Four checking authorities

Use separate computational and dimension scopes. `D` contains dimension names,
`phi` is a face formula over D, `G` is a logical telescope, and `R` is an ordinary
runtime telescope. A runtime usage vector is `u`.

| Judgment | Authority | What success does not authorize |
| --- | --- | --- |
| `D; phi; G |-L t : A`, `t =L s : A` | New logical formation and typed conversion | Runtime values, implicit casts, or effect execution |
| `R |-I A interface`, `A =I B` | Admitted ordinary interface formation/comparison | Identification through logical equivalence or equal layouts alone |
| `R |-R t : A |> u` | Ordinary typing plus quantitative analysis | Purity, invertibility, logical totality, or ownership soundness by itself |
| `Realizes(A, R0, R1, f, c)` | Bridge admission and all independently checked premises | Realization of every logical path |

No equality reflection is added. A path between types is not judgmental equality
of those types. Logical endpoint equations are not optimizer instructions.

The runtime checker currently calls erased inference to expose types and binder
quantities. Erased inference retains quantity annotations. Consequently the
firewall must hold through `Core.Erased`, `Core.Compatibility`, runtime weak-head
inspection, and native layout inspection; putting logical syntax in a separate
module is insufficient. Initially none of these call sites may invoke logical
cubical conversion.

## 2. Initial admitted fragments

The proposed logical kernel has abstract typed parameters, Unit, Bool,
nondependent functions, a predicative universe discipline, dimensions, faces,
and nondependent paths. Universe formation and supported fibrancy must be
explicit in the eventual declarative derivation and checker: an unchecked
annotation `A : U` is not evidence. Composition, dependent PathP, eta, Glue,
univalence, HITs, effects and recursive definitions are deferred. This is a
path fragment, not yet a HoTT implementation.

For the first bridge, admit only a checked pure ordinary grammar: abstract base
parameters with declared logical interpretations, Unit, Bool, nondependent
quantity-annotated functions, variables, lambdas/applications, Unit elimination
and Bool alternatives. Nondependent quantitative products follow only with
corresponding typing, substitution and interpretation arguments. Reject Box,
variants, nominals, dependent runtime families, IO, handles, internal references,
recursion and globals at this bridge. Existing ordinary language features remain
available through the unchanged ordinary pipeline.

Logical evidence initially cannot occur in runtime interfaces. This deliberately
avoids claiming a decidable stability criterion for arbitrary dependent types.
Ordinary erased dependencies remain supported under ordinary checking rules.

## 3. Logical paths

Adopt nondependent path formation, abstraction, application and beta/endpoint
rules from CCHM 2018, section 3, Figure 2 (DOI
[10.23638/LMCS-14(4:5)2018](https://doi.org/10.23638/LMCS-14(4:5)2018)).
Use its free De Morgan interval, face lattice and restricted contexts from
sections 3–4. Do not silently import global regularity or another calculus's
computation rules. Path eta is initially omitted explicitly.

All premises below belong to a well-formed logical context:

```text
A type     a0 : A     a1 : A
--------------------------
Path A a0 a1 type

D,i; phi; G |-L t : A             i fresh; A and G independent of i
D; phi; G |-L t[0/i] =L a0 : A
D; phi; G |-L t[1/i] =L a1 : A
--------------------------------------------------------------
D; phi; G |-L <i>t : Path A a0 a1

p : Path A a0 a1     D |- r : I
--------------------------------
p @ r : A
```

Checked types, not raw endpoint annotations, justify neutral endpoint equations:

```text
(<i>t) @ r =L t[r/i]
p @ 0 =L a0
p @ 1 =L a1
```

Restriction can establish an endpoint equation under a face assumption. Empty
faces do not bypass syntax admission, scoping or context formation. General
systems need coverage and overlap rules; endpoint agreement alone supplies no
interior filler.

The first general demonstration must accept abstract, open examples:

```text
A : U, a,b : A, p : Path A a b
reverse = <i> p @ (~i) : Path A b a
q(i,j) = p @ (i /\ j)
q(0,j) =L a          q(1,j) =L p @ j
q(i,0) =L a          q(i,1) =L p @ i
```

It must not identify `i /\ ~i` with 0 or `(i=0) \/ (i=1)` with the full
face. Boolean vertex enumeration does not decide these De Morgan judgments.

Ordinary term substitution, dimension substitution, restriction and weakening
are distinct operations. Establish their scoping laws and mixed substitution
law, with the required lifting/reindexing under both sorts of binder. Logical
boundary verification does not execute the body multiple times.

## 4. Quantitative foundation and prohibited endpoint rewrite

Use Fibril's actual permission relation `allows p u`: 0 permits 0, 1 permits 1,
and omega permits 0, 1 or omega. It is not the numerical order `0 <= 1 <= omega`.
Compute subterm usage before validating the combined ambient permissions.
Application scales argument demand by the exposed Pi quantity; lambdas retain
capture demand; Bool alternatives join permissions rather than sum executions.

First proof target: typed single-linear substitution for the pure nondependent
fragment. If `t` has usage `(u,1)` in context `G,x:A`, `v:A` has usage `w` in G,
and permissions P admit `u+w`, substitution must yield a well-typed `t[v/x]`
whose demand is admitted by P. State context ordering/lifting precisely in the
formal artifact. Both terms must satisfy fragment admission and internal binder
checks. Then extend to graded simultaneous substitution with typed usage rows.

Do not demand identical inferred vectors for every reduction. An unrestricted
argument may disappear under beta; two alternative branches can use the same
linear variable once per execution. The target is permission-preserving typing
and the stated operational observations, not raw occurrence counting.

This hypothetical runtime rule combination is prohibited:

```text
0 h : H, 1 p : Path H h h |-R p @ 0 : H   -- charge p once
p @ 0 --> h                               -- expose erased h, discard p
```

Initially there is no runtime path application or runtime path value. This blocks
that example but does not by itself prove conversion/erasure safety. Runtime
path closures with logical-only endpoint equality remain a possible later
design, not a refuted alternative. Face-dependent usage is also deferred; it
cannot repair the example merely by recording different demands at endpoints.

## 5. One-way source interpretation

Define a new source interpretation S, not an inverse of machine erasure:

```text
S(Unit) = Unit
S(Bool) = Bool
S(A ->q B) = S(A) -> S(B)
```

Translate admitted terms structurally, preserving Boolean observations. Later
quantitative-product interpretations may retain erased fields as logical ghost
information. Quantities disappear only inside S; ordinary interfaces retain them.
Abstract bases require explicit typed logical interpretations. No general rule
turns a logical shadow into a runtime value.

Required results for the admitted fragment:

```text
G |-R t : R  implies  S(G) |-L S(t) : S(R)
S(t[sigma]) = S(t)[S(sigma)]
```

Specify whether the second equality is literal or a proved structural law.
Also establish preservation of the admitted ordinary computation equations.
These results do not establish runtime preservation or executable adequacy.

## 6. Logical transport before executable certificates

Only after independent logical composition exists may certificates mention
`coe`. Adopt the exact selected CCHM section 4 system/composition rules, including
coverage, overlap agreement and cap/tube compatibility. Specify supported type
formers and composition at abstract fibrant types; do not assume an opaque type
name supplies an executable composition algorithm.

Derive `coe_A x` from logical composition, never from the runtime realizer being
certified. Generic constant-family transport need not reduce judgmentally to x.
A prospective propositional identity proof uses:

```text
h(j) = comp^i A [(j=0) |-> x] x
h(0) =L x
h(1) =L comp^i A [] x
```

This is a derivation to check once composition exists, not a currently checked
proof. Sequential transport and transport along a concatenated type line also
need a comparison theorem; composition of executable maps does not prove it.

An initial realization request contains:

```text
|-R f : R0 ->1 R1             -- exact admitted pure map, no runtime captures
D,i; phi; G |-L A(i) : U
A(0) =L S(R0)                A(1) =L S(R1)
D; phi; G,x:S(R0) |-L c : Path (S(R1)) (S(f) x) (coe_A x)
```

The certificate is open evidence under a fresh logical variable x, not a
term of dependent Pi type: dependent logical functions are not in the initial
grammar. Instantiating this evidence requires the logical typed-substitution
lemma and scope/context rechecking. No new runtime variable or demand is
introduced by the certificate variable.

The bridge separately checks grammar/purity, ordinary interfaces, runtime usage,
logical family formation, endpoint alignment and c. Evidence is bound to the
exact syntax, contexts, definitions and policy. Retain inputs and fully recheck
at consumption initially, or use genuinely opaque checked derivations; today's
public `RuntimeResult` is not such a certificate.

Lower execution to ordinary `Apply f value`, then runtime-check the entire
result in its ambient context. Retain f as computation; dropping its proof must
not recreate a captured environment or erase the map. Open maps require a later
closure/substitution argument. A linear argument alone does not make a closure
reusable, a function pure, or a map invertible.

Realization is partial. For example, a logical shadow of `Sigma 0 Bool 1 Unit`
can retain its Boolean, but the native representation omits it. A runtime inverse
decoder recovering that Boolean cannot be generated from logical equivalence.
A constant decoder may be legal; its certificate cannot assert recovery of an
arbitrary original Boolean. Admit erased products only after their interpretation
extension; retain existing erased-recovery rejection tests immediately.

Before calling this sound executable transport, additionally establish runtime
preservation and an execution/erasure compatibility theorem for a relation between
retained values and logical shadows. The relation may have multiple ghost shadows
per representation, but must preserve the advertised retained observations.
Checked logical specifications alone do not establish this theorem.

## 7. Ownership firewall

Keep acquisition, original-syntax reference admission, region comparison,
identity/current-generation checks, ownership return and cleanup unchanged.
Handles/effects are excluded from the initial realization bridge. A proof cannot
create an internal reference or refresh a stale generation. Runtime registry
rejection is defense in depth, not proof of static linearity.

Nominal singleton region types are not logically inequivalent merely because
their keys differ. Before permitting executable transport through FileHandle,
either retain its prohibition or specify an appropriate rigid/generative brand
discipline. No region representation change is necessary for isolated logical
paths. Ordinary layout equality alone never authorizes a handle cast.

Extend forbidden-reference scanning through every new endpoint, annotation,
family, definition environment and certificate before erasure or reduction.
Preserve skipped-callback capture rejection on failed acquisition. Distinguish
static rejection from trusted runtime tests that deliberately bypass checking.
Cleanup claims remain sequential and limited to represented returns/failures;
no new crash, concurrency or arbitrary-exception guarantee is made.

## 8. Bounded acceptance and evidence

Admission precedes expensive conversion. Traverse all syntax, including dead
branches and erased fields. No unchecked globals initially. Each request shares
a finite work budget; additionally bound input depth/nodes, contexts, dimensions,
substitution output and intermediate normal-form/face expansion. Charge before
allocation. Existing unbounded DNF routines are not production bounded APIs;
checking output size after their execution is insufficient.

Return success with checked evidence, mismatch, unsupported, or limit explicitly.
Only success accepts. A bounded checker can reject inconclusively; this is not a
claim of complete conversion decidability. Limit outcomes never prove equality.

Existing structural Idris substitution proofs and permission algebra lemmas are
useful ingredients, not typed quantitative substitution, erasure or ownership
preservation theorems. Tests find counterexamples and regressions; reviewer
approval and successful builds do not supply missing metatheory.

## Initial implementation slice

`Fibril.Cubical.RuntimeInterface` now admits literal Unit/Bool and recursively
nondependent Pi interfaces, retaining binder quantities in an opaque shape.
It rejects all variables, so abstract bases and dependent interfaces are not yet
supported. It performs no normalization, logical conversion or ordinary checker
calls and is not connected to ordinary runtime acceptance. Comparison admits
both original inputs before comparing their shapes; one shared node-work
allowance covers both admissions and comparison. Unsupported syntax and work
exhaustion are distinct failures, never comparison evidence. The allowance is
not a wall-clock, call-stack or total-allocation guarantee.

This is only the literal-interface part of the proposed firewall: it is not pure
program admission, general-path checking, transport or the full multi-resource
budget policy. `Tests.Cubical.RuntimeInterface` exercises exact work boundaries,
quantities, dependence, effects, handles and unsupported beta wrappers. An
external compile-negative fixture checks constructor opacity. General logical
paths remain unimplemented; the typed foundation below is only a partial step
into proof gate 3.

### Typed quantitative foundation (partial gate 3)

`Fibril.Core.Quantitative.{Syntax,Substitution,Usage}` is an isolated,
Idris-total proof fragment, not a change to ordinary Core checking or reduction.
Its intrinsically simply typed syntax admits Unit, Bool, quantity-annotated
nondependent functions, variables, lambdas/applications, Unit elimination and
Boolean alternatives. Contexts and usage vectors are **newest first**: the
extension written `G,x:A` above is represented by `A :: G`.

The implemented typed theorem is by construction:

```text
sigma : ({A} -> Var G A -> Term D A)
t : Term G B
-----------------------------------
substitute sigma t : Term D B

v : Term G A      t : Term (A :: G) B
-------------------------------------
instantiate v t : Term G B
```

Typed renaming has the analogous result. Lifting preserves the new variable and
weakens every outer replacement under each lambda. Function quantities remain
part of the type indices. These operations impose **no quantitative premises**;
typed renaming/substitution can contract resources or retain invalid internal
binders. They are not quantitative-preservation theorems.

Separately, `Uses t u` gives quantitative derivations with exact `allows` binder
checks, retained captures, scaled application demand and joined alternatives.
`Admits P u` is pointwise permission evidence, not numeric subusage.
`admitJoin` proves that permissions admitting both vectors admit their
alternative join, using `Quantity.joinAllows`. `inferUsage` returns a usage
vector paired with a `Uses` derivation; `checkUsage` additionally returns
`Admits` evidence after checking the combined ambient demand. No completeness
or impossibility theorem for checker failures is claimed. Every argument and
both alternatives require internal quantitative derivations, including arguments
scaled by zero. This is deliberately stricter than `Core.Runtime`, which skips
runtime analysis of erased arguments; no checker correspondence is established.

`weakenUses` proves, for every typed term and `Uses term usage`, the exact
judgment `Uses (weaken term) (Erased :: usage)`. Its stronger helper
`insertUses` inserts exactly one unused variable at any binder depth, preserving
all other demand components. This is not arbitrary renaming: the insertion
cannot contract variables. The proof covers lambdas, application (including
internally checked erased arguments), unit elimination and alternatives. The
`Uses` constructors retain their intermediate usage vectors as explicit
implicit data to support this structural induction.

`addJoinCommon` proves `add (joinQuantity a b) w = joinQuantity
(add a w) (add b w)` for every coefficient; `combineJoinCommon` lifts this
pointwise to usage vectors. `admitJoinParts` proves the converse direction of
`admitJoin`: permission for a join entails permission for each branch. These
are branch-induction ingredients even when the two branches have different
ambient demands, but the common-demand identity does not apply when the
replacement is charged differently in each branch. They do not establish that
substituted subterms have the necessary derivations or common demand.

`usageUnique` proves that any two `Uses` derivations for the same term have
identical vectors. `instantiateHeadUsage` proves the head-reference case of
quantitative substitution: for any typed `v`, derivation `Uses v w` and
`Admits P (combineUsage zeroUsage w)`, it returns `r = w` with
`Uses (instantiate v (Ref Here)) r` and `Admits P r`. This is a genuine
quantitative case, not the general substitution result.

`instantiateAlternativesUsage` additionally proves substitution for the term
`If (Boolean flag) x x`, for any internally valid replacement and any admitted
replacement demand. Its two syntactic copies are alternative executions, so
`joinUsageIdempotent` preserves even a linear demand rather than adding it twice.
This is a strictly bounded term shape, not a general induction theorem.

`substituteUses` now proves the general **single-deletion** graded bound,
not graded simultaneous substitution. A `SingleSubstitution` records a deletion
under an arbitrary retained prefix. `ReplacementUses` records the replacement's
`Uses` derivation at the deletion and its weakening with an erased demand at
each retained binder. For any source derivation, `substituteUses` constructs a
derivation for the substituted term and an `Admits` proof bounding its demand by

```text
retainedDemand s usage + deletedDemand s usage * replacementUsage
```

where the operations are pointwise. This is a permission bound, not an exact
vector equation. It handles every constructor, including internal derivations of
erased arguments, and joins separately charged alternatives using an inequality.
Under a lambda the replacement has erased demand for the retained binder, so
the bound at that binder is its original demand. Transitivity of `allows` then
discharges the binder check; an additional exact-demand invariant is unnecessary.
The path projections commute with addition, scaling and joining; `DemandLeq`
and `Admits` provide the permission preorder and its monotonicity laws.

The requested head theorem is exported as `instantiateLinearUses`:

```idris
{n : Nat} -> {0 context : Vect n Ty} ->
(value : Term context a) -> (body : Term (a :: context) b) ->
(u, w, permissions : Usage n) ->
Uses body (Linear :: u) -> Uses value w ->
Admits permissions (combineUsage u w) ->
(r : Usage n ** (Uses (instantiate value body) r, Admits permissions r))
```

Both `Uses` premises include internal binder checks and derivations for erased
arguments; the context and vectors are newest first. This theorem concerns only
the isolated intrinsically typed fragment. Graded simultaneous substitution, a
`Core.Term` admission/translation connection, checker correspondence, reduction
preservation, erasure compatibility and ownership soundness remain unproved. The
fragment is not a bounded production admission API; gate 3 remains open for its
checker connection.

A stronger *exact* graded substitution formula is false. With context
`[x:Unit, y:Unit]`, `t = If True x y` has demand `[omega, omega]`;
substituting `y` for `x` yields `If True y y` with demand `[1]`, whereas
`u + q*w` predicts `[omega]`. The proved permission bound accommodates this.

`Tests.Quantitative` invokes the general theorem for a checked linear binder,
an erased argument hiding unrestricted occurrences, and shared linear demand
across alternatives. It also invokes the graded single-deletion theorem on the
strict-bound counterexample above. Existing tests cover nested binders, typed
substitution, weakening, permission joins and rejection of invalid binders.

## 9. Execution gates

1. Review this rule sheet; settle concrete syntax, derivations and budget API.
2. Add isolated bounded admission/interface firewall modules and negative tests.
3. Establish the small typed linear-substitution result and checker connection.
4. Add open abstract logical paths, face checking and mixed substitution. No
   new ordinary Core.Term path constructor or runtime conversion authority.
5. Establish S typing/substitution and independently implement logical composition.
6. Check partial realization specifications and lower exact ordinary maps.
7. Establish execution/erasure agreement before trusted transport claims; extend
   through products and fixed-quantity functions before dependent families.
8. Revisit dependent transport, resource families, runtime paths and Glue/univalence
   as explicit proof/design gates, not automatic final implementation tasks.

Proposed module seams: `Fibril.Cubical.{Admission,Budget,RuntimeInterface}`,
`Fibril.Cubical.Logical.{Syntax,Context,Substitution,Conversion,Check}`,
a small `Fibril.Core.Quantitative` proof fragment, then Shadow, System,
Composition, Transport and Lowering. Names are proposals, not existing APIs.

Every milestone includes rejection tests for wrong boundaries, escaped scopes,
erased extraction, changed quantities, captured-map reuse, hidden references,
and exhausted work. General-path tests must use abstract A and neutral p, not
only constants. Keep ownership suites and hosted/native differential fixtures.
Run worktree-local `bash tools/test_cubical_worktree.sh`, then relevant ordinary
and ownership targets (`make test`, `make io-hosted-test`,
`make io-resource-runtime-test`, `make io-resource-emitter-test`). Use `make -j8`
where supported, but do not race shared Pack/build state. Record actual results
and toolchain failures; this contract records no new test pass.

Commit reviewable milestones on feature/cubical-paths. Parallel proof and logical
module work requires stabilized interfaces and isolated writers. Keep shared
manifests, aggregators and ordinary conversion under a single integration writer.

### Structural Core translation (partial checker connection)

`Fibril.Core.Quantitative.CoreTranslation` maps the isolated types, scoped
variables, terms and newest-first contexts to ordinary `Core.Term` and
`Core.Context`. Function and context quantities are retained. The scope length
of each resulting Core term is enforced by its Idris type; `coreContextQuantity`
proves that each translated variable selects the same declared permission. This
is a structural theorem, not Core typing preservation. `Annotations` supplies
application-domain types that the isolated syntax keeps in erased indices;
its constructors are indexed by the exact source term and preserve the domain
index, but no automatic annotation reconstruction is provided.

`Tests.QuantitativeCoreTranslation` compares bounded erased and runtime checker
outcomes and isolated usage for selected open variables, branches, nested
binders, application and Unit elimination. A separate counterexample explicitly
shows isolated rejection of an invalid linear lambda inside an erased argument
while Core runtime accepts the whole term: erased typing still visits the
argument, but runtime usage analysis skips it. These are operational tests, not
an iff or a general one-way checker correspondence theorem. No translation
commutation, general typing/usage preservation, admission from arbitrary Core,
bounded production admission, erasure compatibility, or ownership theorem is
claimed. The checker-connection gate remains open.

### Open neutral-path slice

`Fibril.Cubical.Logical.OpenPath` is a separate, experimental fragment with
one abstract type A, finitely scoped A variables, and one declared neutral path
`p : Path A a b`. Its A-terms are variables and `p @ r`; it checks an
abstraction by endpoint conversion and permits restricted endpoint conversion
on arbitrary scoped faces. Dimension substitution uses the existing scoped
infrastructure; term renaming also renames the path declaration. Scope is
indexed, and the negative fixtures reject escaping dimension and term indices.
The square tests check both zero faces against `a` and both one faces against
`p @ j` and `p @ i` respectively, including mismatch and exhaustion; this is
not a general square or composition judgment.

`convertNeutrals` compares two applications of that same declared path. It
accepts when their interval arguments agree under the face restriction, or when
coincident path endpoints allow both applications to convert to that endpoint.
It does not identify different path variables or claim completeness for all
endpoint-driven equalities. The interval check enumerates the four-element
De Morgan algebra, with the two middle elements fixed by reversal, rather than
Boolean vertices. Face atoms constrain an assigned dimension to an endpoint;
disjunction is checked as a union of such restrictions. The mathematical
justification is that the four-element algebra generates De Morgan algebras,
and each conjunction of endpoint constraints amounts to substituting those
endpoints; a face disjunction is a union of these cases. This is an informal
soundness argument, not a machine-checked theorem.

This is not the complete gate 4: there are no general type contexts, multiple
path variables, path-valued terms, arbitrary term substitution, general term
conversion, type normalization, or checker soundness proofs. `Rejected` means
not accepted by this fragment, not established inequality. Admission limits
face and interval input to a combined 12 nodes per conversion and bounds the
existing exponential face solver's input. For a neutral application, the goal
is the disjunction of the matching endpoint faces (or bottom for a nonmatching
endpoint), so coincident endpoints work under a disjunction of their faces and
empty restrictions still entail the goal. Each extracted endpoint face has at
most as many nodes as the admitted interval; the disjunction therefore has at
most twice that number plus one. The admitted assumption and interval have at
most 12 nodes combined, bounding the assumption and generated goal to at most
24 nodes combined. The neutral-to-neutral check instead admits the face and both interval trees
together at at most `min 12 budget` nodes, before collecting names and
enumerating at most four assignments per distinct occurring dimension. Its
coincident-endpoint fallback calls the existing bounded conversion twice.
Each individual face solver call remains bounded as above. No expanded system
is supplied to either solver. This bounds solver input size, not total work or
its operation count.
Abstraction checks reuse the caller's allowance for each face, so this is not a
shared operation budget. Scope sizes
and Fin index comparison costs are not capped. Substitution
and renaming utilities themselves are not bounded admission APIs. No Boolean
vertex enumeration, ordinary Core paths, conversion changes, or runtime or
ownership authority are involved.

### Multiple open paths (isolated experiment)

`Fibril.Cubical.Logical.PathContext` adds a fixed, non-dependent context of
`m` variables of one abstract type A followed by `k` path declarations whose
endpoints are `Fin m`. Terms use `Fin m`, `Fin k`, and scoped dimensions;
path identity is the declaration index, even when declarations have identical
endpoints. The context is supplied alongside terms: indices are scoped by its
length, not nominally branded to a particular context value. Renaming A-variables
requires renaming both context and terms; dimension substitution is separate.
This is not a general dependent telescope or a production checker.

Conversion reuses OpenPath's four-valued restricted equality for the same path.
Different paths compare only where both compute to a common declared endpoint,
including disjunctive and false faces. Rejection means unsupported, not proven
inequality. The checker caps each context length and dimension count at 12 and
admits at most 12 combined input syntax nodes (and at most the caller allowance)
before bounded solver calls; the allowance is not an exact operation budget.
Abstraction checks each boundary independently, after admitting the original body.
Exhaustion fails closed. There is no soundness theorem or runtime integration.

The compatibility functions above still accept raw context/term pairs. The
additional opaque `CheckedContextAbstraction ctx body l r` binds a successful
boundary check to those exact values; a raw `Accepted` cannot construct it.
`substituteBoundDimensions` substitutes all older dimensions simultaneously,
lifting beneath the bound newest dimension, and rechecks both source and output
before producing a new witness. The existing scoped face substitution acts on
restrictions separately. The combined mixed-substitution examples are tests,
not a proved substitution theorem. Each check preflights its input (including
the transformed body) before solver calls; construction of substitutions and
arbitrary caller-supplied functions are not a bounded public attacker API.
There is no path-variable substitution, general context morphism, formal
composition law, general open path calculus, or runtime authority in this slice.


`substituteBoundDimensionsFinite` is the bounded experimental alternative for
first-order vector environments. It rechecks the source, caps context and
dimension counts at 12 (older input and output dimensions at 11 under the
binder), then shares a node allowance between all environment entries and the
entire substituted output, charging repeated replacements separately. Each vector
cons costs one, each interval constructor in every entry costs one, and each
transformed term and interval constructor costs one. Thus `[Zero]` and a
`Variable` cost three units even when the entry is unused. The transformed
term also has an independent hard cap of 10 nodes, regardless of caller budget:
the source/output checker admits at most 12 combined nodes, including `STop`
and the endpoint `Variable`, so a larger body cannot pass that checker. Only
after this preflight does it construct and recheck the output. This ordering is
established by source inspection; the exhaustion test does not instrument
construction. Unused entries
are still admitted. Vector length fixes the source dimension count; Fin indices
are scoped by the types. The older function-valued API is host-only: arbitrary
functions can perform unbounded work before their results are checked.

The allowance is an admission measure, not a precise runtime or allocation
bound: checks and solver calls have their own allowances, bounded Fin/vector
lookup and weakening incur overhead, and inputs already exist. The source and
output checker retain their fixed 12-node solver-input cap. No total allocation
or formal substitution soundness theorem is claimed.

Finite experimental `ContextMapping` candidates map each A-variable and each
neutral path index with scoped vectors. `checkContextMapping` requires every
source declaration's mapped left and right endpoints to equal the target
path's endpoints in that order. Thus permutations and contractions are
allowed when declarations match, but reversing endpoints is not. Distinct path
indices remain distinct unless explicitly mapped to the same target index.
`mapContextTerm` is raw syntax only. `mapBoundContext` rechecks the exact
candidate, the original abstraction, and the transformed abstraction; it
leaves dimensions untouched, avoiding capture. Its allowance is independently
applied to each check, not a total work budget. Mapping admission costs one unit
per source variable and path entry and caps all four context lengths at 12;
the existing abstraction checker imposes its own syntax and dimension caps.
These facilities do not alter trusted core or runtime paths.

### Open endpoint telescope (experimental)

`Fibril.Cubical.Logical.Telescope` adds a separate first-order A-term fragment
with multiple named paths and open path-application endpoints. An immutable
`Extend` declaration refers only to earlier paths and has no free dimensions;
this rules out circular declarations by construction. Terms and dimensions use
scoped indices. Literal zero and one applications unfold through the telescope,
including chains of older endpoints; otherwise conversion accepts only exact
syntactic identity of the same path and interval. Distinct path names are never
identified merely because their endpoints coincide. Boundary checking substitutes
literal endpoints and checks both sides against open terms.

The separate `convertRestricted` accepts an explicit face. It accepts any terms
on an empty face, identical variables, and applications of the same path at
intervals equal under the face in the four-element De Morgan model. For two
applications it otherwise unfolds either application only when the whole face
entails that interval is zero or one, and continues along the resulting endpoint
chain. For an application versus a variable it compares each declared endpoint
to the variable under the whole face, then checks whether the faces of the
successful endpoints cover the assumption. Thus coincident endpoints can cover
a disjunction of endpoint faces, but that disjunction is not assumed to be top.
Different path identities are not equated except by these justified endpoint
reductions. There is no general branch-refining recursion: for example an
endpoint equal to the target only on its own subface may be missed. Rejection
means unknown, not inequality. The original unrestricted checker remains
syntactic, and neither checker supports path-valued expressions, nested
abstractions, or general typed conversion. `mapDims` is a raw scoped syntactic
operation, not a bounded substitution API or a preservation theorem.

Each checking entry point caps context sizes and dimension counts at 12 and
admits the complete telescope and input terms using one shared 12-node (or
caller allowance) cap before unfolding or boundary substitution. Each later
conversion independently applies the same cap; these are input limits, not an
operation budget. Restricted conversion includes the face in that combined cap;
its generated endpoint tests are bounded by the admitted syntax. Its recursive
comparison has fixed fuel 27, and the standalone restricted interval solver
also checks dimensions and syntax before enumerating assignments. Unfolding and
comparison fail closed on exhaustion. These caps and fuel do not claim a shared
total-work bound. There is no general soundness proof, runtime authority, or
core integration.

### Checked squares (experimental)

`Fibril.Cubical.Logical.Square` checks the explicit nondependent square
fragment over the telescope's abstract A. A body has two bound dimensions
(newest `j`, then `i`); each of its four supplied edges is an A-term abstracted
in the other dimension. The checker weakens each edge under the missing binder
and uses face-restricted conversion to check it against the body on that face.
The opaque `CheckedSquare` is indexed by the exact telescope, body and edges.
It is not an arbitrary higher-path judgment: edges are first-order terms, there
are no path-valued variables, general nested applications, substitution API for
checked squares, dependent path types, or integration with the trusted core.
Rejection may mean conversion is unsupported. Before weakening, one shared
admission allowance counts the complete telescope, body and all four edges,
capped at 16 nodes or the caller allowance, whichever is smaller. This 16-node
cap admits the meet square (13 nodes); each of the four subsequent conversions
independently applies its own 12-node telescope/face/term cap and fuel. These
are not a total-work budget.

### Uniform scoped candidate syntax

`Fibril.Cubical.Logical.ScopedSyntax` represents path families, endpoints,
abstractions, and applications together as expressions, with independently
bounded term and dimension indices. Path families and abstractions bind a
dimension; endpoints do not. The family can mention its bound dimension, so
this permits PathP-shaped dimension-dependent candidates. It does not provide
dependent PathP typing or any surface parser syntax. Dimension substitution
lifts under these binders, and term substitution weakens replacements there. The module proves both substitution identity laws, dimension and term
substitution composition, and their interaction for all scoped expressions.
The interaction substitutes dimensions in each term replacement; the
composition laws act on environments simultaneously. Pointwise congruence and
lifting/weakening lemmas justify the binder cases. Term renaming composes, is
substitution by variables, and commutes with dimension substitution. These are syntactic
candidates only: scope is not typing, and neither a dependent context nor typed
endpoint boundaries, face-restricted conversion, checking, resource accounting,
or soundness is provided. No constructor supplies checked evidence or a runtime
path. Existing first-order checkers are unchanged; no admission guarantee is
claimed for the unbounded structural syntax operations. These structural equations do not establish typing preservation or a checker.

### Pure shadow typing foundation (isolated)

`Fibril.Cubical.Logical.Shadow` defines intrinsic logical Unit, Bool and
nondependent arrow types, variables and terms. `shadowType`, `shadowContext`,
`shadowVar` and `shadowTerm` give a total, structural typing-preserving source
translation for every term in the intrinsic quantitative syntax; arrow
quantities are forgotten and Boolean literals and eliminators are preserved
syntactically. Contexts remain newest first. Because source typing is intrinsic,
this does not assert that arbitrary Core programs are admitted or well typed,
and no `Uses` derivation is needed. `substituteLogical` is a total typed
simultaneous-substitution operation; lifting weakens outer replacements beneath
lambdas. The structural commutation theorem is described below.

`ShadowSubstitution` proves `shadowSubstitutionCommutes` for every source term
and typed simultaneous source substitution, by structural induction. The
explicit source context constructs `imageSubstitution`; this is needed because
forgetting quantities is not injective on types. The theorem is literal Idris
propositional equality, with separate general renaming, weakening, and lifted
environment agreement lemmas. It imposes no quantitative premises.

`ShadowPath` embeds these actual `LogicalTerm` values in a dimension-scoped,
intrinsically typed path-body language. Bodies also include typed neutral path
applications, lambda, nondependent application and eliminators. `ExactPath` is
indexed by both endpoints and requires exact equalities after substituting 0
and 1 into the body. Application substitutes an arbitrary scoped interval;
`pathAtZero` and `pathAtOne` prove the exact endpoint equations. Simultaneous
term and dimension substitution commute for all bodies, and
`substituteExactPath` transports endpoint proofs through logical term
substitution; `substitutePathApplication` proves compatibility with path
application. Neutral path names are scoped by underlying logical type only;
they have no declared endpoint equations here. Hence this is a nondependent,
first-order path slice, not a general path type former, dependent PathP,
face-restricted conversion, or a complete cubical calculus.

This target remains distinct from `TypedPath.NeutralHasType`: the latter has a
fixed abstract-base/path context and untyped `NeutralExpr` syntax, with no Unit,
Bool, arrow or general term context. Conversely `ShadowPath` has no abstract
base or PathP judgments. There is no embedding or proof relating these two
judgments, and no modification of the existing checker. A common typed context,
syntax and conversion theory (including endpoint declarations and substitution)
would be required for that connection. There is no formal ordinary
computation-equation preservation theorem, abstract-base interpretation,
logical-to-runtime reflection, or erasure/execution correspondence. No ordinary
checker or conversion changes.

### Declared shadow endpoints (restricted bridge)

`ShadowPath.PathDeclarations` associates each intrinsically typed neutral path
name with two `LogicalTerm` endpoints in the same ordinary logical context.
Endpoints cannot refer to path names or dimensions. `DeclaredPath` selects the
endpoints by a typed de Bruijn name; `DeclaredEndpoint` derives a left or
right equation only with a proof that `boundedEndpointEntails` accepts. It
preflights the interval (12 nodes) before extracting the endpoint face, then
uses `boundedFaceEntails`; `False` includes exhaustion, not just failure of
entailment. These input-size caps do not bound total work or make the
declarative judgment a resource-bounded runtime checker. `declaredExactApplicationLeft` connects a
literal `ExactPath` application to such an equation. The shadow test uses a
nontrivial conditional from a source context with a checked linear usage.
Term substitution maps both declarations and endpoint derivations, and lifting
by a logical substitution supports capture-avoiding context weakening.
Existing `ExactPath` application and mixed-substitution theorems remain in force.

This is deliberately a restricted declarative interface: endpoint equations
are only for direct neutral applications, not congruence under arbitrary
bodies or lambda binders. Declarations are dimension-independent, and no
face/dimension-substitution preservation theorem for these equations is
claimed (bounded entailment is not automatically preserved by substitution).
`ExactPath` introduction still requires literal endpoint equality, not the new
face equations. General dependent paths, binder-indexed path telescopes,
face-based introduction, dependent contexts, and effects remain unintegrated.
The shadow forgets quantities: none of these judgments establishes runtime
conversion, semantics, resource preservation, or reflection of erased uses.

There is no API reflecting a `shadowTerm` into a source `Uses` derivation;
the negative fixture checks the corresponding type mismatch, not a semantic
nonexistence theorem.
