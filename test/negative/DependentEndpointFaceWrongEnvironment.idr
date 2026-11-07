module DependentEndpointFaceWrongEnvironment

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

admissible : DependentPathAdmissible DependentEndpointFaceWrongEnvironment.allTrue DependentEndpointFaceWrongEnvironment.paths
admissible = DependentAdmissibleCons (HOBool [] True) (HOBool [] True)
  (\_ => Refl) (\_ => Refl) DependentAdmissibleNil

vary : DM -> Bool
vary (False, False) = True
vary (True, True) = True
vary _ = False

otherPath : CommonMorphism
  (commonProductSetoid (commonEnvironmentSetoid []) Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid)
  Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid
otherPath = MkCommonMorphism (\input => DependentEndpointFaceWrongEnvironment.vary (snd input))
  (\rel => cong DependentEndpointFaceWrongEnvironment.vary (snd rel))

otherPaths : carrier (commonDependentPathEnvironmentSetoid [] [LBool])
otherPaths = (DependentEndpointFaceWrongEnvironment.otherPath, ())

otherAdmissible : DependentPathAdmissible DependentEndpointFaceWrongEnvironment.allTrue DependentEndpointFaceWrongEnvironment.otherPaths
otherAdmissible = DependentAdmissibleCons (HOBool [] True) (HOBool [] True)
  (\_ => Refl) (\_ => Refl) DependentAdmissibleNil

valid : DependentEndpointFaceEvidence
  {decls = DependentEndpointFaceWrongEnvironment.allTrue} {face = the (ScopedFace 1) (SEndpoint FZ False)}
  (CommonLeft {i = Var FZ} CommonDeclaredHere Refl)
  (HOPAt [] [LBool] LBool 1 LHere (Var FZ)) (HOPOrdinary [] [LBool] LBool 1 (HOBool [] True))
  DependentEndpointFaceWrongEnvironment.paths DependentEndpointFaceWrongEnvironment.admissible
valid = DepEndpointLeft LHere (Var FZ) (HOBool [] True) CommonDeclaredHere Refl
  DependentEndpointFaceWrongEnvironment.paths DependentEndpointFaceWrongEnvironment.admissible (\env, valuation, holds => AlignBool [] True)

bad : DependentEndpointFaceEvidence
  {decls = DependentEndpointFaceWrongEnvironment.allTrue} {face = the (ScopedFace 1) (SEndpoint FZ False)}
  (CommonLeft {i = Var FZ} CommonDeclaredHere Refl)
  (HOPAt [] [LBool] LBool 1 LHere (Var FZ)) (HOPOrdinary [] [LBool] LBool 1 (HOBool [] True))
  DependentEndpointFaceWrongEnvironment.otherPaths DependentEndpointFaceWrongEnvironment.otherAdmissible
bad = DependentEndpointFaceWrongEnvironment.valid
