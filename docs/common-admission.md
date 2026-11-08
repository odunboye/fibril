# CommonAdmission: bounded typing, face equality and path abstraction

`Fibril.Cubical.Logical.CommonAdmission` admits **typing, first-order face
equality certificates and homogeneous path abstractions**, not a new calculus,
conversion procedure, or production bridge. Common Path v0 in
`cubical-experiment-contract.md` remains authoritative. No v0 rule changed.

## Exact input and successful output

The original typing entry points are:

- `admitCommonTerm budget ctx raw expected`
- `admitCommonPathTerm budget ctx paths dimensions raw expected`

`ctx` and `paths` are separate finite `Vect`s of `LogicalType` (Unit, Bool,
nondependent arrows). `dimensions` is an explicit finite dimension scope.
`AdmissionTerm n` and `AdmissionPathTerm n k d` are **scoped, untyped** annotated
raw syntax. Variables and named paths are `Fin` indices; intervals are actual
`ScopedInterval d` trees, not normalization results. A parser/scoper is not
provided: out-of-scope indices are unrepresentable at this interface.

Every application carries an untrusted domain type annotation. Lambda domains
and result types come from the expected arrow type. Applications check their
function against `domain -> expected` and argument against `domain`. This is an
explicit checking interface, not inference for ambiguous unannotated common
syntax. Wrong annotations fail just like other type mismatches.

Success contains both an accessible actual typing derivation and an accessible
computational semantic witness, indexed by the **same exact** contexts, raw
input's erasure and expected result:

- `AdmittedTerm ctx raw a`: `CommonHasType ctx (eraseAdmission raw) a` and
  `HigherOrderTerm ctx a termTyping`.
- `AdmittedPathTerm ctx paths d raw a`:
  `CommonPathHasType ctx paths (eraseAdmissionPath raw) a` and
  `HigherOrderPathTerm ctx paths a d pathTyping`.

Erasure only removes application annotations and maps constructors; it performs
no reduction or substitution. The caller supplies no target derivation, semantic
conclusion, witness, alignment, model environment, or admissibility certificate.
The checker constructs the evidence. Typed lookup uses `index` on the actual
context, `commonVarAt`, and `commonVarAtIndex` to transport only the syntax index;
it does not confuse indices with types. `commonTypeDecEq` is total constructive
`Dec (a = b)`, including refutations and recursive arrow injectivity.

Ordinary variables, Unit/Bool, lambda/application, if, and unit elimination are
supported. Path terms support ordinary embedding, named application at arbitrary
scoped intervals, and the same lambda/application/if/unit eliminator rules.
Named path environments are retained under ordinary binders, as in v0.

## Limits and rejection

`AdmissionBudget` has two separate allowances:

1. `inputNodes`: one **shared sequential** preflight cap for context cells and
   terminators, all type constructors (including expected and annotated types),
   dimension-scope successors/zero, syntax constructors, index constructors, and
   interval constructors. Every branch is preflighted. This completes before
   type comparison, typed lookup or proof construction.
2. `checkingNodes`: one shared sequential rule-node allowance. Each checked
   ordinary/path node consumes one; ordinary embeddings also consume their
   ordinary subtree's nodes. Siblings receive the preceding sibling's remaining
   allowance, never a fresh copy of the original fuel.

`Left InputLimit`, `Left CheckingLimit`, and `Left TypeMismatch` are distinct
fail-closed results. For these typing entry points, abstraction, globals,
recursion and effects
have no constructors or fallback. The original reflexive equality entry point
below separately reports unsupported endpoint/restriction requests. There is no
production checker/runtime fallback and no solver invoked by these typing entry
points. The separate canonical-context equality entry point explicitly adds a
solver-call allowance and retains authoritative expansion/solver caps, rather
than silently equating them with these two allowances.

This is **not** a whole time/allocation/resource theorem. It does not bound the
caller's construction/deserialization of input, host allocation, compiler
elaboration, interpreting a returned function, or arbitrary host dimension
substitutions. Constructive equality and lookup are total and run after bounded
preflight, but no formal combined cost theorem is claimed. Rejection is not a
proof of semantic inequality or a completeness claim for possible annotations.

## Model assumptions and exact certificate contract

Typing and higher-order witnesses can be constructed without interpreting a
context. The chosen `dependentPathSemantics` interprets the returned witness in
the **environment-dependent** higher-order setoid model. A vector of named-path
types is not a declaration context and asserts no endpoint equations.

The complete declaration/equality/abstraction gate must retain the following
exact v0 evidence, without replacing it with a Boolean. The original reflexive-generator
API, canonical-context equality API and abstraction API below construct items 1–3
for their supported grammars:

1. `CommonDeclarations ctx paths`, each declaration's exact ordinary endpoints,
   their `CommonHasType` derivations and accessible `HigherOrderTerm` witnesses.
2. For each admitted face equality, its exact `CommonFaceEqual` derivation under
   the actual declarations, face, result type and terms; computational witnesses
   for those terms; and `DependentEndpointFaceEvidence` for that derivation and
   those witnesses, indexed by the chosen `ps` and its actual
   `DependentPathAdmissible declarations ps` proof. The certificate constructor
   must work under that explicit assumption; endpoint alignment providers must
   cover the required ordinary environments and face valuations. Applicable
   structural `HigherOrderAlignment` / `HigherOrderPathAlignment` premises must
   also be constructed, not assumed merely from an equal type or erasure.
   Soundness then uses `dependentEndpointFaceEvidenceSound` under its actual
   premises.
3. For homogeneous abstraction, exact `CommonShadowPath` / `CommonAbstract`
   typing and both fresh-dimension face-restricted boundary derivations, plus
   `HigherOrderCommonShadowPath` indexed by that same `ps` and admissibility
   proof. Its exact endpoint/body witnesses require two
   `DependentEndpointFaceEvidence` certificates relating the body to the
   dimension-weakened endpoint witnesses. The existing boundary/application
   theorems apply only to that complete certificate.
4. `DependentPathAdmissible declarations ps` remains an **explicit model
   assumption about a chosen environment-dependent path interpretation** (for the
   canonical API, constructed from its exact-witness canonical validity premise). Its
   endpoint relations for every ordinary environment are not consequences of
   typechecking a list of path types. The checker must not invent an arbitrary
   model, constant path, Boolean certificate, or existence theorem to discharge
   them. Source quantities and `Uses` remain wholly separate.
5. Face entailment needs separate solver caps and rejection for unsupported or
   exhausted checks. Fresh faces conjoin the fresh endpoint to weakened ambient
   restrictions; restriction checks new face entails old face. Dimension mapping
   must rebuild the actual judgments and renew checks/evidence, never assume
   unconditional stability of solver acceptance or semantic certificates.

**Abstraction and both boundary certificates are now constructed automatically**
by the separate canonical-context abstraction API below. Non-reflexive endpoint
equality is supported by the canonical-context equality API; the original
reflexive API is preserved. Existing witness dimension mapping is
available, but is not an admission/resource theorem for host substitutions or
automatic recertification of equality/abstraction boundaries.

## Evidence and regressions

`Tests.Cubical.CommonAdmission` is in the test package and main deterministic
suite. It checks an actual linearly-used source application with an independent
`Uses ... [Linear]` proof and exact source-shadow image, then executes the witness
returned by admission. No source `Uses` proof is a checker input.

The open named-path example depends on both an ordinary Boolean environment and
a dimension. The returned witness is evaluated at **both endpoints**, a
nonvertex, and after dimension substitution through the existing
`mapHigherOrderPathDimensions` theorem. These are executable observations, not
new admitted endpoint equalities or an automatically admitted abstraction.
Ordinary and path binder tests detect capture; nonzero typed indices distinguish
lookup from an index-zero-only implementation.

Runtime negatives cover wrong results, domains, index types and changed contexts,
branch mismatches, checking exhaustion with exact shared branch-fuel boundaries,
and preflight exhaustion on large intervals/types/annotations/dimension scopes.
Diagnostic-specific compile negatives reject out-of-scope ordinary/path/dimension
indices, altered output context/type, `Uses` reflection, and use of an erased
source binder. Equal logical erasures do not recover source binder permissions.

Run sequentially (the script stages this worktree's TTCs privately):

```sh
make -j8 build
bash tools/test_cubical_worktree.sh
```

Broader hosted/native/ownership integration remains a separate production gate.

## Raw equality certificate admission (reflexive generators only)

`admitCommonEquality budget ctx declarations face left right expected certificate`
accepts scoped annotated raw path terms, a finite ordinary type context, raw
`AdmissionDeclarations`, the actual face and expected result type, and a
**first-order** `AdmissionEquality` tree. No input is a target typing derivation,
equality, computational witness, structural alignment, or semantic equation.

`ADCons type left right rest` declares actual annotated ordinary endpoint terms.
Each endpoint is checked independently against that declared type with the prior
ordinary checker; each keeps its accessible `AdmittedTerm` witness. Named types
are derived from those declarations, not supplied as a second unchecked vector.
`checkedDeclarations` constructs the exact authoritative `CommonDeclarations`.
Name lookup therefore checks the actual declared type, including nonzero indices.

Supported certificate constructors are `AERefl`, `AESym`, `AETrans middle c1 c2`,
`AEApp domain cf cx`, `AEIf cc ct cf`, and `AEUnitElim cx cb`. The application domain
must match the retained raw application annotation and checked witness domain.
Congruence constructors must match the raw path constructor; ordinary embeddings
can use reflexivity on arbitrary ordinary lambda/application syntax, but cannot
pretend to be a path congruence constructor. There is no lambda congruence rule,
beta/eta reduction, or new calculus.

**These generators prove no new non-reflexive conversion.** This is certificate
plumbing integrated with the typing checker, not completion of the equality gate.
All supported conclusions have identical annotated endpoints. Constructive
`Maybe (left = right)` checks retain application annotations, indices, Boolean
literals and interval syntax. Every transitivity middle must be that same exact
annotated raw term. Two independently typable terms with the same erasure but
different application-domain annotations are rejected with `SyntaxMismatch`.
A type mismatch reports `TypeMismatch`; neither result proves semantic inequality.

Success, `AdmittedEqualityInput`, retains admitted declarations and
`AdmittedEquality` indexed by those **same** declarations, face, raw endpoints and
expected result. It provides an exact `CommonFaceEqual`, both exact typing and
computational witnesses, and `equalityEvidence`: a function producing
`DependentEndpointFaceEvidence` for **any actual** dependent semantic path
environment `ps` and its `DependentPathAdmissible declarations ps`. The checker
automatically builds self-structural alignments and composes the authoritative
symmetry/transitivity/app/if/unit evidence constructors. Constructive raw equality
allows both endpoints and all transitivity middles to reuse the **same admitted
witness**; no theorem of coherence merely from equal erasure is assumed.
`dependentEndpointFaceEvidenceSound` is directly callable on this returned evidence.
Model admissibility is an allowed interpretation assumption, not an assumption of
the target equality. No manual semantic certificate is needed for success.

### Endpoint/restriction unsupported by the original API

`AEEndpoint name interval side` and `AERestrict source certificate` explicitly
return `UnsupportedEquality`, including when nested. Their full syntax is still
preflighted before that status. There is no endpoint entailment solver or
restriction solver call, and therefore no implicit or uncapped solver fallback.
Any future such solver must expose independent caps; this API claims no solver
completeness or total cost bound.

A raw declaration's canonical admitted endpoint witness does **not** force an
arbitrary `DependentPathAdmissible` proof to select that witness: admissibility
can select differently annotated computational witnesses of the same erased
endpoint. Uniform `HigherOrderAlignment` between such witnesses cannot be
inferred from erasure. Endpoint admission must first index actual admissibility
by canonical admitted witnesses and construct uniform structural alignment
providers (or prove an appropriate coherence result). It must not fabricate
admissibility, request the target semantic equation, or take a manual semantic
certificate. The original API deliberately leaves endpoints unsupported. The separate
canonical-context API below supplies that missing exact-witness contract.

The separate abstraction API below now admits homogeneous abstractions and both
boundaries. Automatic equality dimension recertification remains open. Existing
dimension mapping of returned typing witnesses is tested,
but is not automatic mapping of equality certificates.

### Budgets and evidence

One shared `inputNodes` preflight traverses the ordinary context, declaration
cells/types/**both** endpoint terms, dimension scope, face, both target terms,
expected type, and **all** certificate branches, annotations and middle terms,
including unsupported requests. It finishes before erasure, context derivation,
constructive comparison, or checking. One shared `checkingNodes` allowance then
counts declaration cells (including terminator), all independently checked
endpoint typing nodes, target typing nodes, and certificate nodes. Identical
right/middle typing reuses constructive equality rather than rechecking with
fresh fuel. All siblings receive remaining fuel, never a branch reset.
Structural alignment construction and constructive comparison are bounded by
preflighted syntax but are not separately metered operations; there is no formal
combined time/allocation theorem, evaluation or substitution in admission.

`Tests.Cubical.CommonEqualityAdmission` executes both automatically returned
witnesses of an actual source Boolean `If` with independent `Uses ... [Linear]`,
and invokes authoritative semantic soundness with returned evidence. It checks
arbitrary higher-order lambda/application reflexivity, each congruence, exact
annotation/intermediate/domain/context/name mismatches, unsupported requests and
preflight exhaustion. Exact runtime fuel boundaries are 3/4 for a leaf, 5/6 for
transitivity, 11/12 for conditional congruence, and 9/10 for leaf input preflight.
An open nonconstant named path is observed at both endpoints and after dimension
substitution; `openSound` typechecks the uniform provider under actual model
admissibility. These observations do not assert admitted endpoint equality.
Five new diagnostic-specific compile negatives prevent changing the returned
face, intermediate/right term, type, context, or reflecting equality into `Uses`.


## Canonical-context endpoint and compositional equality admission

`admitCanonicalCommonEquality budget ctx declarations face left right expected certificate`
is a **separate experimental entry point**. It preserves `admitCommonEquality`,
its result types, fuel boundaries, and arbitrary-admissibility reflexive provider.
It uses the same scoped raw syntax, declarations and `AdmissionEquality` grammar;
there are no new v0 equations, lambda congruence, beta/eta, parser, runtime or
production-core changes. Endpoint and restriction requests remain unsupported
by the original entry point, not by this one.

### Exact semantic context premise

`AdmittedDeclarations` retains both actual `HigherOrderTerm` witnesses selected
by declaration checking. `CanonicalPathAdmissible declarations ps` asserts that
**those exact witnesses** are related to the corresponding paths at zero and
one, for every ordinary environment. `ps` is an arbitrary environment-dependent
semantic path environment. Validity is an explicit semantic model premise,
**not** a Boolean algorithm, a target equation, or a promised existence theorem.

`canonicalPathAdmissible declarations ps valid` automatically constructs the
existing `DependentPathAdmissible (checkedDeclarations declarations) ps` using
exactly those witnesses. `CanonicalDeclaredPath` retains exact selected raw
endpoint syntax and witnesses through typed lookup. `canonicalLookupAlignment`,
`canonicalLeftAlignment`, and `canonicalRightAlignment` construct structural
alignment to the witnesses extracted by authoritative lookup/face interpretation
under that very converted admissibility proof. They do not infer coherence from
equal types or erasures. The arbitrary-witness `DependentPathAdmissible` relation
is unchanged and cannot be substituted for canonical validity.

Success is `AdmittedCanonicalEqualityInput`, retaining checked declarations and
`canonicalResult`. That result contains both exact `AdmittedPathTerm` typing and
computational witnesses, `canonicalEquality : CommonFaceEqual ...`, and
`canonicalEvidence`: a provider uniform over `ps` and its actual canonical
validity proof, returning `DependentEndpointFaceEvidence` indexed by the
**automatically converted** admissibility proof. Thus
`dependentEndpointFaceEvidenceSound (canonicalEvidence result ps valid)` proves
the returned terms related at every ordinary environment and every De Morgan
valuation satisfying the admitted face. No caller target typing, equality,
alignment or semantic certificate is accepted by admission.

### Raw certificates and supported closure

`AEEndpoint name interval side` checks that the left target is exactly
`APAt name interval`, the named declaration's actual result type matches the
expected type, and the right target is `APOrdinary` of its selected declared
endpoint. Raw matching retains **all annotations**, literal values, finite names,
and interval syntax, even when different annotations have identical erasures.
Every declaration's two endpoints is independently typechecked before lookup.
The actual `boundedEndpointEntails face interval side = True` proof is checked
and retained; failure, including solver exhaustion/incompleteness, rejects.
Both `CommonLeft` and `CommonRight` are constructed with their exact witnesses
and automatic canonical alignment providers.

Symmetry, transitivity and app/if/unit-eliminator congruences operate on genuinely
**different** target terms, without a top-level raw-equality requirement.
Transitivity recursively admits both sides of its exact annotated middle, then
structurally compares their actual witnesses, including every hidden application
domain, to construct the required intermediate alignment. It fails closed if
comparison cannot construct alignment. Reflexivity alone requires exact annotated
raw equality and shares its single checked witness. Application congruence checks
both raw domain annotations and the certificate domain.

`AERestrict source certificate` checks the exact authoritative
`boundedFaceEntails target source = True`, admits the subcertificate at `source`,
and constructs `CommonRestrict` / `DepEndpointRestrict`. The implication is
**target => source**, never the reverse. No automatic certificate substitution
or dimension recertification is supplied.

### Shared allowances and rejection

`CanonicalEqualityBudget` contains the original `syntaxBudget : AdmissionBudget`
and a separate `solverCalls` allowance. One shared sequential input preflight
traverses the ordinary context, every declaration/type/both endpoints, dimension
scope, ambient face, both annotated targets, expected type, and the entire
certificate tree including middle terms, source faces and intervals. It finishes
**before** checking declarations, lookup, comparisons, or any solver call.

One shared `checkingNodes` allowance then pays for declaration cells/terminator,
independently checked ordinary endpoints, every certificate node, and the ordinary
or path nodes visited by reflexivity's typing checker. Endpoint certificates
reuse checked declaration witnesses; their target embeddings/name witnesses are
constructed by the certificate rule rather than independently rechecked.
Congruences construct their target typing from admitted children. Recursive
siblings and restrictions receive remaining fuel, never a reset.

One `solverCalls` token is reserved per endpoint/restriction request, shared
across all siblings. Additionally the **existing authoritative fixed caps**
remain: endpoint interval preflight 12, combined face-node cap 12, dimension cap
12. There is no uncapped solver or expansion fallback. `InputLimit`,
`CheckingLimit`, `SolverLimit`, `TypeMismatch`, `SyntaxMismatch`, and
`FaceMismatch` are fail-closed results. `FaceMismatch` includes inconclusive or
capped solver rejection and is not a proof of non-entailment. The original
entry point continues to use `UnsupportedEquality` for endpoint/restriction.
Comparisons, alignment construction and interpreting returned providers are not
separately metered; this is not a whole allocation/time theorem.

### Evidence and remaining gate

`Tests.Cubical.CommonEndpointAdmission` invokes the automatically returned
provider under a **constructively built canonical validity proof** for an actual
open, nonconstant, environment-dependent Boolean path from the ordinary variable
to the shadow of a linear source Boolean `If`. `Uses ... [Linear]` remains a
separate proof. Both endpoints and both ordinary Boolean valuations are checked,
while another dimension has a non-Boolean value. Symmetry, transitivity,
app/if/unit congruences, restriction, and nonzero named lookup invoke semantic
soundness too. Returned witness dimension mapping is observed separately, not
claimed as admitted equality recertification.

Regressions reject wrong face/name/type/interval/context/endpoint annotation,
reversed restriction, missing solver tokens, interval/face solver caps, and
shared input/checking exhaustion. Exact small endpoint boundaries are input
16/17 and checking 4/5; trans/sym checking is 7/8, and solver tokens are shared
across trans/sym, restrictions and all congruence siblings. Diagnostic-specific
compile negatives prevent changing returned context/face or replacing canonical
validity by arbitrary `DependentPathAdmissible` evidence.

**Remaining:** there is no general conversion/equality decision procedure or
completeness theorem, no general existence theorem for semantic contexts, no
lambda equality rule, or automatic recertification of arbitrary
dimension-mapped equalities. The separate
abstraction API below completes the bounded raw abstraction gate, not production
integration.

## Canonical-context homogeneous abstraction admission

`admitCanonicalCommonAbstraction budget ctx declarations ambient left right body expected zero one`
accepts only raw scoped inputs: endpoints at dimension scope `d`, a body at
`S d`, and **two** raw `AdmissionEquality n k (S d)` certificates. It accepts
no target derivation, equality, computational witness, structural alignment or
semantic model. The original APIs and their exact budget boundaries are unchanged.

`weakenAdmissionPath` shifts every existing dimension by `Var . FS`, including
under ordinary lambdas, without changing ordinary indices or application domain
annotations. `eraseWeakenAdmissionPath` proves that its actual erasure is exactly
`mapCommonPathDimensions (Var . FS)`. The two certificates are checked at the
actual faces `SConjunction (weakenFace ambient) (SEndpoint FZ False/True)` against
the retained body and respective weakened endpoint, not at the ambient face alone.
Declarations, endpoints and body are independently checked at the expected type.

Success retains `abstractionDeclarations` and `abstractionResult`. The latter
contains all three exact computational typing witnesses, `abstractionZero` and
`abstractionOne`. `abstractionPath result` constructs **the actual** `CommonAbstract`
with that exact raw body, endpoints and returned boundary derivations.
`abstractionEvidence result ps valid` automatically produces
`HigherOrderCommonShadowPath (abstractionPath result) ps
(canonicalPathAdmissible declarations ps valid)` for arbitrary actual `ps` and
its exact `CanonicalPathAdmissible` premise. There is no assertion that this model
exists for every raw declaration context.

Boundary checking may select different typing derivations from retained body and
mapped endpoint witnesses. Admission inspects the actual computational witnesses,
including hidden application domains, to construct structural alignments on
**both sides of both boundaries**, then uses `DepEndpointAlign`. Equality of
logical types or erasures is never used as a unique-typing/coherence assumption.
Failure to build alignment rejects with `SyntaxMismatch`.

### Preflight, expansion and shared budgets

The existing `CanonicalEqualityBudget` is reused, with no resetting public wrapper
calls. One shared input preflight visits context, every declaration/type/both
ordinary endpoints, dimension scope, ambient face, expected type, both path
endpoints, body, and **both complete certificate trees**, including annotations,
restriction faces and transitivity middle terms. This finishes before any
endpoint dimension expansion, erasure, checking, comparison or solver call.

After original-input preflight, the remaining `inputNodes` must conservatively
reserve the expansion output: twice each original raw endpoint size, twice each
ambient face size **for each boundary**, and six nodes for the two conjunctions,
endpoints and `FZ`s. Each shifted dimension index adds only one `FS`, so this
bounds output size before constructing either weakened endpoint/face. This
fixed weakening admits no arbitrary host substitution environment. A reservation
failure is `InputLimit`, not an uncapped expansion fallback. Expansion has a
separate accounting phase within `inputNodes`, not a new incompatible budget field.

One sequential `checkingNodes` allowance pays for declarations, independent
endpoint/body typing, then first and second internal canonical equality checks.
The second check receives the first check's remaining rule fuel **and** solver
allowance. Existing fixed authoritative face/interval/dimension solver caps also
apply. All exhaustion rejects; there is no runtime/conversion fallback.
Canonical equality's `TypeMismatch`, `SyntaxMismatch`, `FaceMismatch` (including
capped/inconclusive solver rejection), `CheckingLimit` and `SolverLimit` semantics
are unchanged. The original equality API still uses `UnsupportedEquality` for
endpoint/restriction requests. No lambda equality or beta/eta rule was added.
Comparison, alignment and provider interpretation are not separately metered;
these reservations are not a formal combined host allocation/time theorem.

### Executable and diagnostic evidence

`Tests.Cubical.CommonAbstractionAdmission` admits the actual nonconstant `λi. p i`
from an ordinary Boolean variable to the shadow of a source linear Boolean `If`.
`Uses ... [Linear]` and its source image remain separate proofs. It constructs a
canonical model for the checked declarations, invokes the returned semantic
provider, checks both endpoints and both ordinary Boolean environments, and
observes the exact returned application witness. The ambient face constrains an
older dimension, while another older dimension is off-diagonal. Application
soundness uses `higherOrderCommonPathApplicationRelated` directly; endpoint
application soundness composes that theorem with `higherOrderCommonPathBoundary`,
with **no manual witness alignment**. The convenience theorem
`higherOrderCommonPathApplicationBoundary` currently exposes a private generated
case during normalization for an opaque returned witness in this Idris compiler;
the test uses the two authoritative constituent theorems instead, without
changing their API or claiming that convenience-call gate passed.

Additional checks cover application/lambda/transitivity boundary alignment,
an arrow body capturing the ordinary context, dimension-dependent endpoints and
capture-avoiding weakening, wrong boundaries/faces/dimensions/context/result,
same-erasure annotation ambiguity, and complete preflight before checking.
Exact small-case input/reservation and checking boundaries are **31/32** and
**12/13**; the second boundary exhausts shared checking/solver allowances.
Seven diagnostic-specific compile negatives protect exact face, endpoint, body,
result type, ordinary context, dimension scope and canonical admissibility.

This is bounded admission for the frozen grammar, not general conversion,
completeness, arbitrary equality dimension recertification, a semantic-context
existence theorem, a full cubical model, or a production integration theorem.
