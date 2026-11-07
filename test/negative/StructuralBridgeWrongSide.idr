module StructuralBridgeWrongSide
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

-- Concrete evidence demonstrates that the symbolic premises are inhabited.
originalExample : boundedEndpointEntails (the (ScopedFace 1) SBottom) (Var FZ) False = True
originalExample = Refl
restrictionExample : TypedPath.boundedFaceEntails (the (ScopedFace 1) SBottom) SBottom = True
restrictionExample = Refl
wrongExample : boundedEndpointEntails (the (ScopedFace 1) SBottom) (Var FZ) True = True
wrongExample = Refl

-- Every check is supplied independently with its precise index; no solver
-- result is asserted by reflexivity for an unknown face.
bad : (face, other : ScopedFace 1) ->
  (original : boundedEndpointEntails face (Var FZ) False = True) ->
  (restriction : TypedPath.boundedFaceEntails face face = True) ->
  (wrong : boundedEndpointEntails face (Var FZ) True = True) ->
  BridgeableEquality {context = [LBool]} {l = LHere} {r = LHere}
    (BodyRestrict {face} {source = face}
      (BodyEndpoint (DeclaredLeft {face} {i = Var FZ} DeclaredHere original)) restriction)
    (NApply (NPath FZ) (Var FZ)) (NBase FZ)
bad face other original restriction wrong = BridgeRestrictLeft wrong
