module StructuralBridgeWrongConstructor
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

source : BodyEqual (DeclarePath (LRef LHere) (LRef LHere) NoPaths)
  (the (ScopedFace 1) SBottom) (NeutralAt LHere (Var FZ)) (Embed (LRef LHere))
source = BodyEndpoint (DeclaredRight DeclaredHere Refl)

-- Both endpoint checks pass on bottom, but the indexed constructor is right.
bad : BridgeableEquality StructuralBridgeWrongConstructor.source (NApply (NPath FZ) (Var FZ)) (NBase FZ)
bad = BridgeEndpointLeft
