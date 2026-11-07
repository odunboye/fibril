module DependentEndpointFaceWrongAdmissibility

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

admissible : DependentPathAdmissible DependentEndpointFaceWrongAdmissibility.declarations DependentEndpointFaceWrongAdmissibility.paths
admissible = DependentAdmissibleCons DependentEndpointFaceWrongAdmissibility.boolDomain DependentEndpointFaceWrongAdmissibility.boolDomain
  (\_ => Refl) (\_ => Refl) DependentAdmissibleNil

otherAdmissible : DependentPathAdmissible DependentEndpointFaceWrongAdmissibility.declarations DependentEndpointFaceWrongAdmissibility.paths
otherAdmissible = DependentAdmissibleCons DependentEndpointFaceWrongAdmissibility.boolDomain DependentEndpointFaceWrongAdmissibility.boolDomain
  (\() => Refl) (\() => Refl) DependentAdmissibleNil

boolAlignment : HigherOrderAlignment DependentEndpointFaceWrongAdmissibility.boolDomain DependentEndpointFaceWrongAdmissibility.boolDomain
boolAlignment = AlignApplication (AlignLambda (AlignBool _ True)) (AlignLambda (AlignVar _ _ LHere))

valid : DependentEndpointFaceEvidence
  {decls = DependentEndpointFaceWrongAdmissibility.declarations} {face = the (ScopedFace 1) (SEndpoint FZ False)}
  (CommonLeft {i = Var FZ} CommonDeclaredHere Refl)
  (HOPAt [] [LBool] LBool 1 LHere (Var FZ))
  (HOPOrdinary [] [LBool] LBool 1 DependentEndpointFaceWrongAdmissibility.boolDomain)
  DependentEndpointFaceWrongAdmissibility.paths DependentEndpointFaceWrongAdmissibility.admissible
valid = DepEndpointLeft LHere (Var FZ) DependentEndpointFaceWrongAdmissibility.boolDomain CommonDeclaredHere Refl
  DependentEndpointFaceWrongAdmissibility.paths DependentEndpointFaceWrongAdmissibility.admissible (\env, valuation, holds => DependentEndpointFaceWrongAdmissibility.boolAlignment)

bad : DependentEndpointFaceEvidence
  {decls = DependentEndpointFaceWrongAdmissibility.declarations} {face = the (ScopedFace 1) (SEndpoint FZ False)}
  (CommonLeft {i = Var FZ} CommonDeclaredHere Refl)
  (HOPAt [] [LBool] LBool 1 LHere (Var FZ))
  (HOPOrdinary [] [LBool] LBool 1 DependentEndpointFaceWrongAdmissibility.boolDomain)
  DependentEndpointFaceWrongAdmissibility.paths DependentEndpointFaceWrongAdmissibility.otherAdmissible
bad = DependentEndpointFaceWrongAdmissibility.valid
