module DependentEndpointFaceWrongSide

import Data.Vect
import Data.Fin
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Face
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

allTrue : CommonDeclarations [] [LBool]
allTrue = CommonDeclarePath (CBool True) (CBool True) CBoolType CBoolType CommonNoPaths

paths : carrier (commonDependentPathEnvironmentSetoid [] [LBool])
paths = (commonConstant True, ())

admissible : DependentPathAdmissible DependentEndpointFaceWrongSide.allTrue DependentEndpointFaceWrongSide.paths
admissible = DependentAdmissibleCons (HOBool [] True) (HOBool [] True)
  (\_ => Refl) (\_ => Refl) DependentAdmissibleNil

noHolds : False = True -> Void
noHolds Refl impossible

validRight : DependentEndpointFaceEvidence
  {decls = DependentEndpointFaceWrongSide.allTrue} {face = the (ScopedFace 1) SBottom}
  (CommonRight {i = Var FZ} CommonDeclaredHere Refl)
  (HOPAt [] [LBool] LBool 1 LHere (Var FZ))
  (HOPOrdinary [] [LBool] LBool 1 (HOBool [] True))
  DependentEndpointFaceWrongSide.paths DependentEndpointFaceWrongSide.admissible
validRight = DepEndpointRight LHere (Var FZ) (HOBool [] True) CommonDeclaredHere Refl
  DependentEndpointFaceWrongSide.paths DependentEndpointFaceWrongSide.admissible
  (\env, valuation, holds => void (DependentEndpointFaceWrongSide.noHolds holds))

bad : DependentEndpointFaceEvidence
  {decls = DependentEndpointFaceWrongSide.allTrue} {face = the (ScopedFace 1) SBottom}
  (CommonLeft {i = Var FZ} CommonDeclaredHere Refl)
  (HOPAt [] [LBool] LBool 1 LHere (Var FZ))
  (HOPOrdinary [] [LBool] LBool 1 (HOBool [] True))
  DependentEndpointFaceWrongSide.paths DependentEndpointFaceWrongSide.admissible
bad = DependentEndpointFaceWrongSide.validRight
