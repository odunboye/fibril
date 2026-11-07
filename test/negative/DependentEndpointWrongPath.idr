module DependentEndpointWrongPath

import Data.Vect
import Data.Fin
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Foundation.DeMorgan.Face
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

twoPaths : CommonDeclarations [] [LBool, LBool]
twoPaths = CommonDeclarePath (CBool True) (CBool True) CBoolType CBoolType
  (CommonDeclarePath (CBool True) (CBool True) CBoolType CBoolType CommonNoPaths)

headPath : CommonDeclaredPath DependentEndpointWrongPath.twoPaths LHere (CBool True) (CBool True)
headPath = CommonDeclaredHere

tailPath : CommonDeclaredPath DependentEndpointWrongPath.twoPaths (LThere LHere) (CBool True) (CBool True)
tailPath = CommonDeclaredThere CommonDeclaredHere

paths : carrier (commonDependentPathEnvironmentSetoid [] [LBool, LBool])
paths = (commonConstant True, (commonConstant True, ()))

admissible : DependentPathAdmissible DependentEndpointWrongPath.twoPaths DependentEndpointWrongPath.paths
admissible = DependentAdmissibleCons (HOBool [] True) (HOBool [] True) (\_ => Refl) (\_ => Refl)
  (DependentAdmissibleCons (HOBool [] True) (HOBool [] True) (\_ => Refl) (\_ => Refl) DependentAdmissibleNil)

validHead : True = True
validHead = dependentDeclaredLeftAlignedAtFace DependentEndpointWrongPath.headPath DependentEndpointWrongPath.paths
  DependentEndpointWrongPath.admissible () (\_ => (False, False))
  (the (ScopedFace 1) (SEndpoint FZ False)) (Var FZ) Refl Refl (HOBool [] True) (AlignBool [] True)

validTail : True = True
validTail = dependentDeclaredLeftAlignedAtFace DependentEndpointWrongPath.tailPath DependentEndpointWrongPath.paths
  DependentEndpointWrongPath.admissible () (\_ => (False, False))
  (the (ScopedFace 1) (SEndpoint FZ False)) (Var FZ) Refl Refl (HOBool [] True) (AlignBool [] True)

bad : (ps : carrier (commonDependentPathEnvironmentSetoid [] [LBool, LBool])) ->
  (adm : DependentPathAdmissible DependentEndpointWrongPath.twoPaths ps) ->
  (alignment : DependentEndpointAlignment (HOBool [] True)
    (dependentDeclaredLeftAtFace DependentEndpointWrongPath.tailPath ps adm () (\_ => (False, False))
      (the (ScopedFace 1) (SEndpoint FZ False)) (Var FZ) Refl Refl)) ->
  related (commonTypeSetoid LBool)
    (applyMorphism (applyMorphism (commonDependentPathLookup [] [LBool, LBool] LBool LHere) ps) ((), (False, False)))
    (applyMorphism (higherOrderTermSemantics (HOBool [] True)) ())
bad ps adm alignment = dependentDeclaredLeftAlignedAtFace DependentEndpointWrongPath.tailPath ps adm ()
  (\_ => (False, False)) (the (ScopedFace 1) (SEndpoint FZ False)) (Var FZ) Refl Refl
  (HOBool [] True) alignment
