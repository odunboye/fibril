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
