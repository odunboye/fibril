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
They do not establish independent substitution preservation of declared path
abstractions or their face equalities. There is no claim of correspondence with
production Core or runtime behavior.
