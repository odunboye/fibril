module ShadowTypedBridgeWrongIndex
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Foundation.DeMorgan.Face

import Fibril.Cubical.Logical.PathContext
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

-- Valid source endpoint evidence for the second variable, not the first.
source : DeclaredEndpoint
  (DeclarePath (LRef (LThere LHere)) (LRef (LThere LHere)) NoPaths)
  (the (ScopedFace 1) (SEndpoint FZ False))
  (NeutralAt LHere (Var FZ)) (Embed (LRef (LThere LHere)))
source = DeclaredLeft DeclaredHere Refl

bad : NeutralEqual (bridgeContext {context = [LBool, LBool]} LHere (LThere LHere))
  (the (ScopedFace 1) (SEndpoint FZ False)) (NApply (NPath FZ) (Var FZ)) (NBase FZ) NType
bad = bridgeLeft {context = [LBool, LBool]} LHere (LThere LHere) (SEndpoint FZ False) (Var FZ)
  source Refl
