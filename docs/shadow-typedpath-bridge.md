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

This is not a path interpreter or a semantic soundness theorem, nor does it
establish derivation coherence, endpoint admissibility, runtime behavior,
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
