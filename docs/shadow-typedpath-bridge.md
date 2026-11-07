# Restricted shadow–typed path bridge

`Fibril.Cubical.Logical.ShadowTypedBridge` connects a specific declared shadow
path to `TypedPath.NeutralHasType`. The source has one declaration whose two
endpoints are references of the same logical type. `variableIndex` retains the
references' context positions; `bridgeContext` creates the corresponding
single target neutral-path declaration. The target's `NType` is an abstract
base: this interpretation does not identify its values with booleans, units,
or functions, and does not interpret the other logical operations.

`endpointEntailsFace` proves for every scope, face, interval, and side that
source endpoint acceptance implies target face acceptance. The proof analyzes
the interval preflight; it needs no target hypothesis or runtime assumptions.
The converse is not asserted.

`bridgeLeft` and `bridgeRight` take a source `DeclaredEndpoint` and a
side-indexed witness selecting its actual constructor, then derive the target
check. This changes their earlier signatures, which required a separate target
check. The constructor witness is necessary: if the declared endpoints are
identical, a right-constructor endpoint proof can inhabit the left endpoint
judgment even when the left face check fails, and conversely. No arbitrary
`DeclaredEndpoint` implies acceptance of a chosen side.
`NeutralShadowWitness` selects the source abstraction `p @ i` and its actual
endpoint-rule proofs; `bridgeDeclaredPath` derives both target boundary checks
from those proofs and requires no target judgments. The newer `bridgeAbstract` translates its actual boundary proofs using
`BridgeableEquality`; it is not a translator for arbitrary `BodyEqual` or
`DeclaredShadowPath` proofs.

The tests give a quantitative `Ref Here` with an actual linear `Uses` proof,
its shadow declaration and abstraction, both endpoint conversions and the
resulting target typing. The pre-existing linear example using `If` and Boolean
literals is **not** supported: target syntax has no Boolean operations or
literal endpoints. Also unsupported are general path telescopes, logical
binders and applications, general proof congruence, constant
abstraction translation, and dependent family translation. This is not a
resource-preservation theorem, runtime equality, or an ownership change.

The source endpoint check first admits the interval with `intervalNodes 12`
and then calls `TypedPath.boundedFaceEntails` on the same face and endpoint.
Consequently a valid source endpoint check cannot fail the bridge's target
check at those same arguments. The abstraction witness uses the same checks
at each binder face, so it cannot provide such a counterexample either. The
wrong-face negative test therefore independently constructs a valid source
endpoint at the left face and tests the target guard at the opposite face;
it does not claim that source evidence for that opposite face exists.
The wrong-index fixture supplies valid source endpoint evidence for a different
declaration and checks its rejection by the bridge.


`BridgeableBody` relates source variable positions and the one neutral path
application to target expressions. `BridgeableEquality` indexes the actual
source derivation, face, and target expressions. `BridgeTrans` composes two
bridgeable proofs with the same target intermediate; `BridgeRestrict` translates
a bridgeable proof at its original face and carries the source restriction
proof unchanged to `NEqualRestrict`. Both `BodyRestrict` and `NEqualRestrict`
require exactly `boundedFaceEntails target source = True`. There is no extra
admission step, solver transitivity assumption, or unchecked face removal.
The older specialized certificates remain available; restricted endpoint
certificates independently recheck the endpoint at the target face.

`NeutralEqual` already had symmetry; it now also has declarative transitivity
and guarded restriction, analogous to source equality and target typing
restriction. `boundedFaceEntailsSound` proves accepted entailments sound for
the documented four-valued face semantics, including the finite bounds; a
rejected check may reflect exhaustion. This does not prove semantic soundness
of the enlarged typing/equality calculus. The proof-producing experimental
checker is unchanged and does not search these new closure rules; production
runtime conversion is unchanged. Other source congruence constructors remain
outside this bridge, and bridgeability is not claimed for every source proof.

## Common face-restricted equality

`CommonDeclarations` independently stores arbitrary ordinary `CommonTerm`
endpoints, with typing evidence in the exact ordinary context and a separate
indexed path context. These endpoints do not depend on dimensions or mention
path names. `commonDeclarations` translates every source declaration, and
`commonDeclaredPath` preserves its typed path index and both endpoints.

`CommonFaceEqual` is an independent declarative judgment over typed common path
terms, indexed by the exact declaration context, face and logical type. Its
endpoint rules use common lookup evidence and the same `boundedEndpointEntails`
equation as the source; restriction uses the same `boundedFaceEntails`
equation. Reflexivity requires common typing, while the other constructors
preserve typing through their premises or typed declarations. The structural
`commonDeclaredEndpoint` and `commonBodyEqual` translations cover all source
`DeclaredEndpoint` and `BodyEqual` constructors, including all three source
congruences. They do not embed a source equality proof as a target axiom.
The tests include the shadow of an actual linear Bool conditional, as a
nonconstant declaration endpoint and within a conditional congruence.

This judgment provides face-restricted equality; the abstraction translation
described below builds on it. Neither this judgment nor the shadow reflects to quantitative
`Uses`, runtime equality, or semantic soundness. Negative fixtures check wrong
face, path index, type, and attempted `Uses` reflection.

`CommonShadowPath` is an independent common-syntax abstraction with typed,
possibly non-ordinary endpoints and checked boundaries at the weakened ambient
face conjoined with the fresh dimension endpoint. `commonDeclaredShadowPath`
translates both source boundaries; application substitutes in common syntax and
commutes with source translation. Endpoint application requires the source
`DimensionEvidence` certificate: budgeted entailment is not automatically
stable under substitution. The separate source `Uses` derivation is not
reflected by this logical judgment. This does not provide general PathP,
semantics or ownership, or an embedding into all of `TypedPath`.

## Quantitative substitution paired with a declared common path

`commonQuantitativeSubstitution` takes an actual `Uses term usage` and
`ReplacementUses s replacement` for an arbitrary `SingleSubstitution s`, and
an arbitrary `DeclaredShadowPath` over the shadow of the same source context.
It returns the existing `substituteUses` result, common typing of the actual
substituted source term, and the common translation of the path after logical
substitution by the source substitution's image. The path is not required to
have the source term as an endpoint. The face and dimension scope are unchanged.

The returned `SubstitutionResult` retains the source theorem's actual result
usage and its `Admits` bound, exactly
`combineUsage (retainedDemand s usage) (scaleUsage (deletedDemand s usage) replacement)`;
this is a permission bound, not an equality of usage vectors. Nothing about
logical typing or equality establishes `Uses`. The paired Bool conditional
fixture separately checks all three projections, and an equality links its
substituted source shadow to that fixture's left path endpoint. Negative
fixtures reject a changed substituted endpoint and a mismatched ordinary context.

This result translates an already-substituted logical path. Separately,
`commonSubstitutionCommutes` and `commonPathSubstitutionCommutes` relate
independent common substitution to translation of logical terms and path bodies.

## Independent common substitution preservation

`CommonSubstitutionTyped` relates arbitrary source and target ordinary contexts
by typing each image at the exact source variable's type. It does not require a
logical substitution or recover quantitative evidence. Under one such
common environment, `substituteCommonDeclarations` maps each declaration's
actual endpoints and typing evidence, and `substituteCommonDeclaredPath`
preserves the exact path name, type, and mapped endpoints. Path names and
dimensions are not substituted by this operation.

`substituteCommonFaceEqual` recursively preserves every common equality
constructor, including endpoint checks, restriction, transitivity, and
congruences. Its face is unchanged, so the existing solver equations are
reused at precisely their original arguments. `substituteCommonShadowPath`
maps an independently supplied common abstraction, its actual body and both
boundaries at the weakened ambient face. `commonPathMixedSubstitution` supplies
the needed commutation between term substitution and dimension weakening;
`substituteCommonShadowApplication` proves application commutation. A test
constructs a common abstraction directly, with endpoints depending on an
ambient dimension, and checks its mapped declaration, both weakened boundaries,
and application. These proofs do not wrap a source equality derivation.

`commonQuantitativeIndependentPath` pairs the existing source substitution
result and source-to-common substitution commutation with preservation of an
independently supplied common path. It uses the common image of the same source
substitution, and explicitly requires the original `Uses` and `ReplacementUses`
evidence. The independent path need not be translated from a source path or
have the source term as an endpoint. The result retains the existing source
usage bound; common typing and equality do not imply usage evidence.

These results are declarative; they do not establish semantic soundness,
general PathP, correspondence with production Core or runtime equality,
resource enforcement at runtime, or an ownership change.

### Pair-model endpoint soundness and remaining gap

`commonBoundedEndpointValSound` proves that an accepted bounded endpoint
check forces the interpreted interval to the requested endpoint at every
satisfying valuation in the solver's four-pair De Morgan model. It connects
`boundedFaceEntailsSound` to the actual `faceAtVal` endpoint observations and
uses `dmScopedEndpointValSound`; dimensions may take either non-endpoint pair.
The extracted endpoint face is sufficient, not necessary, for an interval to
be an endpoint in this model.

The independent `FirstOrderTerm` and `FirstOrderPathTerm` interpretations cover
the structurally restricted Bool/Unit fragment, indexed by actual common typing
derivations; lambda and application are excluded. Typed finite environments
interpret ordinary variables, and named paths are functions of the ordinary
environment and the actual four-pair dimension value. `FirstOrderAdmissible`
requires each path's endpoint values to equal its actual declared endpoint
interpretations for every ordinary environment; `firstOrderDeclaredLookup`
returns these endpoint equations for a declared path.

`commonFaceValEntailsSound` transports a bounded face entailment at the same
four-pair valuation. `firstOrderDeclaredLeftAtFace` and
`firstOrderDeclaredRightAtFace` combine admissible lookup with endpoint
soundness: on a satisfying face, the path value at the interpreted interval
equals the interpretation of a first-order witness for the corresponding
actual declared endpoint. The returned witness need not be the witness chosen
by a separate equality derivation.

`firstOrderTermCoherent` and `firstOrderPathCoherent` prove that independent
first-order witnesses for the same typed syntax have equal interpretations,
including for arbitrary four-pair valuations. The proof reifies each witness’s
syntax and uses constructor injectivity rather than inspecting erased typing
derivations.

`FirstOrderFaceEqual` gives derivation-indexed evidence for reflexivity,
symmetry, transitivity, restriction, declared left and right endpoints, and
conditional and unit-elimination congruence.
`firstOrderFaceEqualSound` proves equal interpretations on a satisfying face
for any admissible path environment. Transitivity uses witness coherence;
endpoint cases use admissible declaration lookup. Congruence uses actual
subderivations and coherence between independently chosen witnesses. The unit
interpreter ignores the scrutinee but the body relation is proved recursively.
Application congruence is excluded: `firstOrderPathApplicationImpossible`
shows that an application typing derivation cannot have a first-order witness. It is not a soundness theorem for every
`CommonFaceEqual` derivation.
This interpretation does not claim higher-order, dependent path, composition,
resource, or runtime soundness.
The result is not a soundness theorem for the full path calculus and makes no
claim about higher-order semantics, ownership, or runtime behavior.

### Higher-order setoid foundation

`commonTypeSetoid` assigns Bool and Unit equality setoids and recursively
assigns arrow types a setoid of relation-preserving morphisms. Arrow relation
compares outputs on *related*, potentially distinct inputs. Reflexivity uses
morphism preservation; symmetry and transitivity use the component setoid
laws. `commonApplicationCongruence` is the resulting application rule. This
is constructive and does not assume equality of Idris functions.

`HigherOrderTerm ctx type typing` is an explicit, runtime-accessible witness
indexed by the actual `CommonHasType` derivation. Its constructors retain the
context, result type and, at lambda and application, the domain type. This is
an extra premise: an erased typing derivation does not automatically provide
such a witness. `higherOrderTermSemantics` structurally interprets the witness
as a context-to-result setoid morphism, using lookup, constants, currying,
application, Boolean conditionals, and unit elimination. The latter requires
both typed witnesses even though its semantics returns the body. Conditional
branches can have arbitrary logical types, including arrows.

`higherOrderApplicationBeta` proves that interpreting an application is
semantic application, for arbitrary witnesses and logical types;
`higherOrderApplicationBetaAt` gives the corresponding pointwise equation.
Their proof splits the result logical type to expose the interpreter’s
dependent case tree. Neither law assumes equality of semantic functions.

`HigherOrderAlignment` is structural evidence indexed by two actual ordinary
witnesses for the same syntax, context and result type. Its application rule
requires a shared domain type, recursively, and its lambda, conditional and
unit-elimination rules align their children. It has no semantic-relation
premise. `higherOrderAlignedVariableRelated` proves the variable case over
related environments; `higherOrderApplicationRelated` and
`higherOrderChoiceRelated` prove value-level application and conditional
congruence. `higherOrderAlignedRelated` proves recursive semantic coherence for all ordinary
alignment constructors, across arbitrary related environments, using the setoid
relation rather than function equality. Corresponding dependent-path alignment
and its semantic coherence are not yet established.
In particular this does not assert coherence for differently typed intermediate
expressions.

This is not a path interpreter or a semantic soundness theorem, nor does it
establish unrestricted derivation coherence, endpoint admissibility, runtime behavior,
ownership, or a general HoTT or cubical model. The existing first-order path
interpretation remains separate.

`HigherOrderPathTerm ctx paths type dimensions typing` is an explicit witness
indexed by the actual erased `CommonPathHasType` derivation; it cannot be
recovered by inspecting erased typing evidence. Its semantics is an extensional
morphism on the product of the ordinary environment and a named-path
environment. Each path is an extensional morphism from the equality setoid on
four-pair `DM` to the result type setoid. The path environment is independent
of the ordinary environment and is retained unchanged when a lambda extends
that environment. `CPAt` uses `evalDMVal` at the supplied valuation. This is an
interpretation; general face-equality soundness for higher-order paths is not
established here.

The higher-order path environment is independent of the ordinary environment.
`HigherOrderAdmissible` therefore requires each actual declared endpoint to be
related to the fixed path endpoint for **every** ordinary environment. This is
inhabited for suitable constant endpoints (including constant conditionals),
but variable-dependent endpoints may make it uninhabited. In particular,
for a Bool variable endpoint, applying the same zero-endpoint obligation to
the environments `(False, ())` and `(True, ())` would equate False and True;
`higherOrderVariableEndpointNotAdmissible` proves this for any fixed Bool path.
This is a universal requirement over ordinary environments for one fixed path
environment, not a requirement merely at the environment used in a judgment.
Unlike the first-order path environment, it cannot in general model the translated linear
conditional endpoint uniformly. `higherOrderDeclaredLookup` preserves the
actual declaration index and endpoint syntax; the left and right face lemmas
return a witness for that syntax and a target-setoid relation at the valuation.
They do not yet compare that witness with an independently chosen witness:
higher-order coherence and general higher-order face-equality soundness remain
unproved. In particular, application syntax does not determine its intermediate
argument type, so a proof cannot assume typing uniqueness or simply align the
application subterms by syntax injectivity.

### Environment-dependent named paths

The separate `commonDependentPathEnvironmentSetoid` interprets each named
path as a setoid morphism from the product of the ordinary environment and
four-pair interval to its declared type. Its environment relation is
pointwise extensional. `weakenDependentPaths` pulls these morphisms back along
the projection that drops a fresh ordinary binder, and
`dependentPathSemantics` uses that weakening under lambdas. Admissibility and
endpoint lookup are indexed by the actual common declarations; the face
endpoint lemmas use the existing bounded face solver. The linear-source test
constructs a path with variable-dependent Boolean endpoints and different
values at non-Boolean dimensions, and checks capture avoidance.

This is isolated from the earlier environment-independent model and does not
establish general higher-order face equality soundness or witness coherence.

`dependentPathSameWitness` exposes the preservation property of the dependent
interpreter at two related ordinary/path environments and one valuation. Both
sides must use the **same witness**; it is not coherence for independently
constructed witnesses, even when their erased derivation indices coincide. The
checked application `(λx.true) (λy.y)` has witnesses at Bool with intermediate
argument types `Bool -> Bool` and `Unit -> Unit`, which are provably distinct.
Thus unannotated syntax and result type cannot justify alignment. General
coherence needs either a justified way to align the erased derivation indices
or explicit structural alignment, including intermediate application types;
endpoint soundness additionally needs alignment with the witness actually
chosen by admissibility. Neither is supplied by this same-witness lemma.

`DependentEndpointAlignment` now indexes a structural alignment by the actual
endpoint evidence extracted from a particular admissibility proof.
`dependentDeclaredLeftAlignedAtFace` and `dependentDeclaredRightAlignedAtFace`
use it to relate the declared path endpoint to an independently selected witness;
the alignment is an explicit premise, not a semantic equality assumption. These
lemmas are pointwise at one ordinary environment.

`DependentFaceEvidence` is indexed by an actual `CommonFaceEqual` derivation
and selected dependent path witnesses. Its soundness theorem covers structural
reflexivity, symmetry, transitivity and face restriction at one environment,
path environment, admissibility proof and valuation. Reflexivity and the
intermediate witnesses in transitivity require explicit path alignment; no
semantic relation is assumed. Endpoint, application, conditional and unit
elimination derivations are not yet constructors of this evidence, so this is
not general higher-order face soundness.

A separate `DependentEndpointFaceEvidence` is indexed by the actual path
environment and admissibility proof. It adds left and right endpoints with a
uniform provider of structural alignment to the exact extracted endpoint
witness, plus symmetry, transitivity, restriction, application, conditional and
unit elimination congruences; it embeds the original structural fragment.
`DepEndpointAlign` transports evidence to structurally aligned selected
witnesses without assuming semantic relations. Its soundness theorem uses no
target semantic relation as a premise. This remains evidence-indexed, not
general face soundness.

### Valuation lemmas and remaining boundary gap

`commonIntervalWeakeningVal` and `commonFaceWeakeningVal` preserve observations
under a fresh dimension; `commonEndpointFaceHolds` establishes the corresponding
boundary face. `dependentPathValuationCongruence` relates interpretations of the
**same witness** at pointwise-equal valuations and related environments.

`mapHigherOrderPathDimensions env witness` now computes a
`HigherOrderPathWitness ctx paths type targetDimensions
(mapCommonPathDimensions env originalTerm)`. This record contains an erased
`CommonPathHasType` derivation and its accessible `HigherOrderPathTerm`, indexed
directly by that exact transformed syntax. No syntax equality or semantic
conclusion is assumed. Recursion inspects only retained witness constructors,
not erased typing derivations. Ordinary higher-order witnesses are reused;
named-path intervals use actual `substituteScoped`; lambda, application,
conditional and unit elimination rebuild their target derivations and witnesses.

`commonIntervalSubstitutionVal` proves substitution evaluation structurally for
all four De Morgan pairs. `dependentPathDimensionsRelated` then relates the
**mapped witness** at a target valuation to the original at the composed
valuation `\i => evalDMVal targetValuation (env i)`, across related ordinary
and dependent named-path environments. Lambda cases pull both path environments
back with `weakenDependentPaths`; application cases cover unit, Boolean and
arrow results without function equality or function extensionality.
`dependentPathWeakeningRelated` specializes this to `Var . FS` and
`extendCommonValuation value valuation`, for any fresh pair value.

`dependentPathBoundaryRelated` consumes `DependentEndpointFaceEvidence` for an
actual derivation

```text
CommonFaceEqual decls
  (SConjunction (weakenFace face) (SEndpoint FZ side))
  body (mapCommonPathDimensions (Var . FS) endpoint) type
```

with selected body and mapped endpoint witnesses and the actual dependent path
environment/admissibility proof. When the ambient face holds, it derives the
relation between body interpretation at `extendCommonValuation (side, side)
valuation` and the **unweakened** endpoint interpretation at `valuation`. The
proof composes face-evidence soundness with weakening preservation; it does not
require the desired relation as a premise. This is one evidence-indexed boundary,
not a general interpretation of every `CommonShadowPath`.

`HigherOrderCommonShadowPath path ps adm` now packages computational body and
endpoint witnesses with `DependentEndpointFaceEvidence` for **both actual
boundary derivations** of the exact `CommonAbstract`. Its path, dependent path
environment and admissibility proof are indices, not interchangeable premises.
`higherOrderCommonPathBody` and `higherOrderCommonPathEndpoint` interpret these
selected witnesses; `higherOrderCommonPathBoundary` proves their endpoint
relation at every ambient valuation satisfying the abstraction's face.

`higherOrderCommonPathApplication w i` computes a `HigherOrderPathWitness` indexed
by **`applyCommonShadowPath path i` itself**, by mapping the retained body witness
with `atDimension i`. Fresh de Bruijn `FZ` becomes `i`; every older `FS v` becomes
`Var v`. `higherOrderCommonPathApplicationRelated` proves that interpreting this
exact application under the original valuation is related to
`higherOrderCommonPathBody w (extendCommonValuation (evalDMVal valuation i)
valuation)`. It uses `dependentPathDimensionsRelated`, then pointwise identity
substitution evaluation (`commonApplicationValuation`) and valuation congruence,
not function equality or function extensionality. The coordinate may evaluate
to any of the four De Morgan pairs; no ambient face is required for agreement.

`higherOrderCommonPathApplicationBoundary w side` specializes application to
`Zero`/`One` and composes that agreement, in the application-to-body direction,
with the actual abstraction boundary theorem using setoid transitivity. Under
`faceAtVal valuation face = True`, the actual application interpretation is
related to the selected original left/right endpoint at the original valuation.
This includes arrow values via setoid relations, not equality of functions.

These are application and boundary semantics **only with explicit semantic
evidence**. General `CommonFaceEqual` soundness is not proved, so this evidence
cannot currently be extracted for arbitrary `CommonAbstract` boundaries. Nothing
here proves free cubical/CCHM presheaf naturality, composition, univalence,
transport, or a runtime authority; production conversion and execution are unchanged.
The finite pair-valuation substitution theorem below is a narrower result.

Regression proofs in `Tests.Shadow` cover an exact transformed lambda/app/if
witness, a nonconstant ordinary-environment-dependent named path, related but
distinct path/function environments, non-Boolean substitutions, all application
result types, unit elimination, the actual linear source witness, fresh-index
weakening, and left/right evidence-indexed boundary transport. Application
regressions additionally cover a nonconstant conditional path with actual linear
Bool If endpoints in both ordinary environments, non-Boolean interiors distinct
from the endpoints, CPAt endpoints retaining an older dimension under a
nontrivial ambient face, and a lambda/arrow-valued path. Their conclusions use
the generic exact-application theorems. The negative
`HigherOrderDimensionWrongIndex` fixture checks that weakening cannot be
misindexed at the fresh dimension instead of the older `FS FZ` dimension.
`CommonApplicationWrongCoordinate`, `CommonApplicationWrongFace`, and
`CommonApplicationWrongPathWitness` require specific diagnostics for a changed
application coordinate, a false ambient face, and evidence for a different exact
path, respectively. `tools/test_cubical_worktree.sh` checks these in the fresh
worktree-package suite, rejecting unrelated type/import errors.

### Finite pair-valuation naturality of application

`liftCommonDimensions sigma` fixes the fresh dimension `FZ` and maps `FS v`
to `weakenInterval (sigma v)`. For **every** finite scoped substitution
`sigma : Fin d -> ScopedInterval e`, interval `i`, and body `b`, the structural
substitution composition/congruence laws prove `commonPathApplicationDimensions`:

```
mapCommonPathDimensions sigma (mapCommonPathDimensions (atDimension i) b)
  = mapCommonPathDimensions (atDimension (substituteScoped sigma i))
      (mapCommonPathDimensions (liftCommonDimensions sigma) b)
```

This is syntax equality, not an evaluation-only wrapper. Its fresh/older-index
square is `commonApplicationDimensionSquare`. `commonShadowApplicationDimensions`
specializes it to the body of the actual abstraction. The independently mapped
right-hand syntax is called `commonShadowMappedBodyApplication`; that name does
**not** promise a typed reindexed path abstraction.

`dependentPathDimensionsSquareRelated` proves computational witness coherence
for any syntactically commuting dimension-substitution square. Both routes
actually run `mapHigherOrderPathDimensions` twice, retaining their independently
rebuilt typings. The proof composes dimension-substitution semantics with
pointwise valuation congruence; it neither identifies typing proofs nor equates
functions. `dependentPathApplicationDimensionsRelated` specializes this square
to application. `higherOrderCommonPathApplicationDimensionsRelated` then relates
mapping the **actual** `higherOrderCommonPathApplication w i` witness to
`higherOrderCommonPathMappedBodyApplication w sigma i`, which independently maps
the retained body under the fresh binder and applies it at `substituteScoped
sigma i`. Relations hold as setoid morphisms, including related ordinary/path
environments and arrow-valued captured bodies.

`higherOrderCommonPathApplicationNaturality` also relates the mapped actual
application under target valuation `nu` to the original application under the
**composed actual valuation** `\v => evalDMVal nu (sigma v)`. No face assumption
or admissibility at a different path environment is invented. Both off-diagonal
pairs `(False, True)` and `(True, False)` are allowed; this is not just Boolean
vertex agreement.

#### Explicit recertification of declarative path dimensions

`mapCommonFaceEqualDimensions sigma target eq cert` constructs an independent
`CommonFaceEqual` for the selected mapped terms at the exact target face. Its
`CommonDimensionEvidence sigma target eq` is indexed by the original derivation,
not merely its conclusion. It recursively mirrors **all** equality rules:

- Refl retains the original erased typing witness and maps it with
  `mapCommonPathDimensionsTyped`; ordinary terms and path lookup are unchanged.
  That typing map includes ordinary lambdas, but there is **no lambda equality
  rule**.
- Left/Right retain the actual declared-path lookup and require a fresh proof of
  `boundedEndpointEntails target (substituteScoped sigma i) side = True`.
- Restrict recertifies the child at `substituteScopedFace sigma source` and
  requires the exact renewed
  `boundedFaceEntails target (substituteScopedFace sigma source) = True`.
- Sym, Trans, App, If and UnitElim recursively rebuild their target derivations.

`CommonPathDimensionEvidence sigma path` supplies this evidence for both original
boundaries under `liftCommonDimensions sigma`, at the substituted original
boundary faces. `mapCommonShadowPathDimensions sigma path cert` then constructs
an actual `CommonAbstract`, with result type:

```
CommonShadowPath decls (substituteScopedFace sigma face)
  (mapCommonPathDimensions sigma left)
  (mapCommonPathDimensions sigma right) a
```

Its actual body is `mapCommonPathDimensions (liftCommonDimensions sigma) body`;
its two checked boundaries have exactly that body and the weakened mapped
endpoints. No target boundary equality is accepted as an assumption in lieu of
recertifying the original rules. The syntactic alignment uses:

- `commonEndpointSubstitution` and its weakening specialization
  `commonEndpointWeakening`;
- `commonFaceLiftWeakening` and `commonBoundaryFaceDimensions`, proving
  substitution of `weakenFace face /\ (FZ = side)` equals
  `weakenFace (substituteScopedFace sigma face) /\ (FZ = side)`;
- `commonPathLiftWeakening`, aligning mapped weakened endpoints with weakened
  mapped endpoints.

`commonMappedShadowApplicationDimensions` proves the application substitution
square with the **actual recertified target path**, not just body syntax.

This API is **declarative, conditional, and caller-supplied**. There is no new
computational proof search, finite-vector recertifier, or cost-bound claim here;
the source `ShadowSubstitutionBounds` wrappers are not an independent-common
checker. Every required renewed bounded check must be proved at its precise
index. An unsupported entailment or exhausted existing solver budget prevents
construction of the certificate, even if the entailment is mathematically
valid. In particular, the simple solver cannot prove a disjunction from the
identical disjunction; a Meet/Reverse image of an accepted source endpoint can
therefore fail. A long Reverse chain can also fail interval preflight. This is
**not unconditional substitution stability** of bounded entailment.

Tests construct actual mapped paths for a 2 -> 1 contraction with a nonconstant
linear-source Bool If endpoint, a 1 -> 2 expansion of a translated source path
with a nontrivial ambient face, and an independent path with dimension-dependent
`CPAt` endpoints (including a Meet/Reverse image). They extract the actual body
and both boundaries, and evaluate a computational witness indexed by the actual
mapped application on both off-diagonal pairs and both ordinary Bool inputs.
Additional compile-time tests cover every equality rule and typed lambda
mapping. Diagnostic-gated negatives cover an equivalent but different original
derivation, the wrong substitution index, a
failed endpoint face, a failed renewed restriction, interval-budget exhaustion,
and an unsupported mapped disjunction.

##### Declared endpoint result-type correction

Previously the endpoint constructors had the abbreviated signature:

```
CommonLeft : CommonDeclaredPath decls p l r -> boundedEndpointEntails face i False = True ->
  CommonFaceEqual decls face (CPAt (variableIndex p) i) (CPOrdinary l) a
```

(and Right analogously). The inferred type of `p` did not constrain the result
`a`: a Bool path could incorrectly yield an equality labeled `LUnit`. The
corrected signatures explicitly bind `{0 a : LogicalType}` and
`{0 p : LogicalVar paths a}` (with the corresponding contexts/endpoints) before
the lookup premise; Left/Right now have the declared path's actual type. Both
wrong-result-type fixtures were accepted when only the original signatures were
restored, and both are rejected with the correction. The remaining
`CommonFaceEqual` constructors were audited: Refl ties its result to its typed
witness; Sym/Trans/Restrict retain their premise type; App uses the arrow result;
If and UnitElim retain their branch type. No other constructor signature change
was needed.

#### Still unsupported: automatic higher-order path witness reindexing

There is still no unrestricted `CommonShadowPath` dimension-map API, and no new
`HigherOrderCommonShadowPath` map. The declarative result above does **not** supply
`DependentEndpointFaceEvidence` indexed by its exact target derivations, the
independently mapped computational body/endpoint witnesses, or actual `ps, adm`
admissibility evidence. Source semantic boundary evidence is not a target
certificate. `HOCommonAbstract` reconstruction remains a separate obligation.
The application witness tests do not assert automatic mapping of a complete
higher-order path witness.

These results are naturality of a **finite four-pair valuation interpretation**.
They do not establish naturality of free De Morgan cubical/CCHM presheaves, nor
composition/filling, univalence, or runtime transport. No production checker,
conversion, evaluator, or runtime was changed.

Regression proofs contract dimensions `2 -> 1` for the nonconstant Bool `If`
path with actual linear-source endpoints, expand `1 -> 2` for the captured
arrow-valued body, use `Meet`/`Reverse`, and check both off-diagonal valuations
and both captured Bools. They check fresh, older, and oldest indices under the
lift, syntax interchange, witness interchange, and composed valuations. Negative
fixtures reject an uncomposed source valuation and an unsubstituted coordinate
for the mapped-body API; the fresh-worktree runner checks their exact failure
site and diagnostic, excluding unrelated import/type-declaration failures.
