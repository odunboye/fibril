module DependentEndpointWrongFace

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

admissible : DependentPathAdmissible DependentEndpointWrongFace.allTrue DependentEndpointWrongFace.paths
admissible = DependentAdmissibleCons (HOBool [] True) (HOBool [] True)
  (\_ => Refl) (\_ => Refl) DependentAdmissibleNil

rightCheck : boundedEndpointEntails (the (ScopedFace 1) (SEndpoint FZ True)) (Var FZ) True = True
rightCheck = Refl

validRight : True = True
validRight = dependentDeclaredRightAlignedAtFace CommonDeclaredHere DependentEndpointWrongFace.paths
  DependentEndpointWrongFace.admissible () (\_ => (True, True))
  (the (ScopedFace 1) (SEndpoint FZ True)) (Var FZ) DependentEndpointWrongFace.rightCheck Refl
  (HOBool [] True) (AlignBool [] True)

bad : True = True
bad = dependentDeclaredLeftAlignedAtFace CommonDeclaredHere DependentEndpointWrongFace.paths
  DependentEndpointWrongFace.admissible () (\_ => (True, True))
  (the (ScopedFace 1) (SEndpoint FZ True)) (Var FZ) DependentEndpointWrongFace.rightCheck Refl
  (HOBool [] True) (AlignBool [] True)
