module StructuralBridgeWrongIndex
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Cubical.Logical.PathContext
import Fibril.Foundation.DeMorgan.Face

import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

source : BodyEqual (DeclarePath (LRef (LThere LHere)) (LRef (LThere LHere)) NoPaths)
  (the (ScopedFace 1) (SEndpoint FZ False)) (NeutralAt LHere (Var FZ)) (Embed (LRef (LThere LHere)))
source = BodyEndpoint (DeclaredLeft DeclaredHere Refl)

-- The valid source refers to a different declaration and endpoint index.
bad : NeutralEqual (bridgeContext {context = [LBool, LBool]} LHere (LThere LHere))
  (the (ScopedFace 1) (SEndpoint FZ False)) (NApply (NPath FZ) (Var FZ)) (NBase FZ) NType
bad = bridgeEquality {context = [LBool, LBool]} LHere (LThere LHere) _
  {source = StructuralBridgeWrongIndex.source} BridgeEndpointLeft
