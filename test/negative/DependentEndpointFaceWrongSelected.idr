module DependentEndpointFaceWrongSelected

import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Foundation.DeMorgan.Face
import Data.Vect
import Data.Fin
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge


boolDomain : HigherOrderTerm [] LBool
  (CApplicationType {a = LArrow LBool LBool} (CLambdaType (CBoolType {b = True})) (CLambdaType (CVariable LHere)))
boolDomain = HOApplication [] (LArrow LBool LBool) LBool
  (HOLambda [] (LArrow LBool LBool) LBool (HOBool [LArrow LBool LBool] True))
  (HOLambda [] LBool LBool (HOVar [LBool] LBool LHere))

unitDomain : HigherOrderTerm [] LBool
  (CApplicationType {a = LArrow LUnit LUnit} (CLambdaType (CBoolType {b = True})) (CLambdaType (CVariable LHere)))
unitDomain = HOApplication [] (LArrow LUnit LUnit) LBool
  (HOLambda [] (LArrow LUnit LUnit) LBool (HOBool [LArrow LUnit LUnit] True))
  (HOLambda [] LUnit LUnit (HOVar [LUnit] LUnit LHere))

declarations : CommonDeclarations [] [LBool]
declarations = CommonDeclarePath (CApp (CLam (CBool True)) (CLam (CVar FZ)))
  (CApp (CLam (CBool True)) (CLam (CVar FZ)))
  (CApplicationType {a = LArrow LBool LBool} (CLambdaType (CBoolType {b = True})) (CLambdaType (CVariable LHere)))
  (CApplicationType {a = LArrow LBool LBool} (CLambdaType (CBoolType {b = True})) (CLambdaType (CVariable LHere))) CommonNoPaths

paths : carrier (commonDependentPathEnvironmentSetoid [] [LBool])
paths = (commonConstant True, ())

admissible : DependentPathAdmissible DependentEndpointFaceWrongSelected.declarations DependentEndpointFaceWrongSelected.paths
admissible = DependentAdmissibleCons DependentEndpointFaceWrongSelected.boolDomain DependentEndpointFaceWrongSelected.boolDomain
  (\_ => Refl) (\_ => Refl) DependentAdmissibleNil

boolAlignment : HigherOrderAlignment DependentEndpointFaceWrongSelected.boolDomain DependentEndpointFaceWrongSelected.boolDomain
boolAlignment = AlignApplication (AlignLambda (AlignBool _ True)) (AlignLambda (AlignVar _ _ LHere))

valid : DependentEndpointFaceEvidence
  {decls = DependentEndpointFaceWrongSelected.declarations} {face = the (ScopedFace 1) (SEndpoint FZ False)}
  (CommonLeft {i = Var FZ} CommonDeclaredHere Refl)
  (HOPAt [] [LBool] LBool 1 LHere (Var FZ))
  (HOPOrdinary [] [LBool] LBool 1 DependentEndpointFaceWrongSelected.boolDomain)
  DependentEndpointFaceWrongSelected.paths DependentEndpointFaceWrongSelected.admissible
valid = DepEndpointLeft LHere (Var FZ) DependentEndpointFaceWrongSelected.boolDomain CommonDeclaredHere Refl
  DependentEndpointFaceWrongSelected.paths DependentEndpointFaceWrongSelected.admissible (\env, valuation, holds => DependentEndpointFaceWrongSelected.boolAlignment)

bad : DependentEndpointFaceEvidence
  {decls = DependentEndpointFaceWrongSelected.declarations} {face = the (ScopedFace 1) (SEndpoint FZ False)}
  (CommonLeft {i = Var FZ} CommonDeclaredHere Refl)
  (HOPAt [] [LBool] LBool 1 LHere (Var FZ))
  (HOPOrdinary [] [LBool] LBool 1 DependentEndpointFaceWrongSelected.unitDomain)
  DependentEndpointFaceWrongSelected.paths DependentEndpointFaceWrongSelected.admissible
bad = DepEndpointLeft LHere (Var FZ) DependentEndpointFaceWrongSelected.unitDomain CommonDeclaredHere Refl
  DependentEndpointFaceWrongSelected.paths DependentEndpointFaceWrongSelected.admissible (\env, valuation, holds => DependentEndpointFaceWrongSelected.boolAlignment)
