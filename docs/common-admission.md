# CommonAdmission: bounded typing and reflexive equality admission

`Fibril.Cubical.Logical.CommonAdmission` admits **typing and a reflexive-generator
equality certificate slice**, not a new calculus,
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
have no constructors or fallback. The equality entry point below separately
reports unsupported endpoint/restriction requests. There is no production
checker/runtime fallback and no solver invoked by these entry points. Thus there
is no solver invocation or expansion budget in the supported slice. Such budgets
must be explicit before
those operations are added, not silently equated with these two allowances.

This is **not** a whole time/allocation/resource theorem. It does not bound the
caller's construction/deserialization of input, host allocation, compiler
elaboration, interpreting a returned function, or arbitrary host dimension
substitutions. Constructive equality and lookup are total and run after bounded
preflight, but no formal combined cost theorem is claimed. Rejection is not a
proof of semantic inequality or a completeness claim for possible annotations.

## Model assumptions and remaining certificate gate

Typing and higher-order witnesses can be constructed without interpreting a
context. The chosen `dependentPathSemantics` interprets the returned witness in
the **environment-dependent** higher-order setoid model. A vector of named-path
types is not a declaration context and asserts no endpoint equations.

The complete declaration/equality/abstraction gate must retain the following
exact v0 evidence, without replacing it with a Boolean. The reflexive-generator
slice below now constructs items 1 and 2 for its supported grammar:

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
   assumption about a chosen environment-dependent path interpretation**. Its
   endpoint relations for every ordinary environment are not consequences of
   typechecking a list of path types. The checker must not invent an arbitrary
   model, constant path, Boolean certificate, or existence theorem to discharge
   them. Source quantities and `Uses` remain wholly separate.
5. Face entailment needs separate solver caps and rejection for unsupported or
   exhausted checks. Fresh faces conjoin the fresh endpoint to weakened ambient
   restrictions; restriction checks new face entails old face. Dimension mapping
   must rebuild the actual judgments and renew checks/evidence, never assume
   unconditional stability of solver acceptance or semantic certificates.

**Non-reflexive endpoint equality and abstraction certificate construction
remain unimplemented.** Raw declaration endpoint typing and the bounded
reflexive-generator equality slice below are automatic. Existing witness
dimension mapping is
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

### Unsupported endpoint/restriction and the remaining gate

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
certificate. This slice deliberately leaves endpoints unsupported until then.

Homogeneous abstraction, automatically admitted boundaries, equality dimension
recertification, non-reflexive open named-path equality, and the full first
end-to-end path gate remain open. Existing dimension mapping of returned typing
witnesses is tested, but is not automatic mapping of equality certificates.

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
