module DependentCongruenceWrongAdmission

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

admissible : DependentPathAdmissible DependentCongruenceWrongAdmission.declarations DependentCongruenceWrongAdmission.paths
admissible = DependentAdmissibleCons DependentCongruenceWrongAdmission.boolDomain DependentCongruenceWrongAdmission.boolDomain
  (\_ => Refl) (\_ => Refl) DependentAdmissibleNil

otherAdmissible : DependentPathAdmissible DependentCongruenceWrongAdmission.declarations DependentCongruenceWrongAdmission.paths
otherAdmissible = DependentAdmissibleCons DependentCongruenceWrongAdmission.boolDomain DependentCongruenceWrongAdmission.boolDomain
  (\() => Refl) (\() => Refl) DependentAdmissibleNil

boolAlignment : HigherOrderAlignment DependentCongruenceWrongAdmission.boolDomain DependentCongruenceWrongAdmission.boolDomain
boolAlignment = AlignApplication (AlignLambda (AlignBool _ True)) (AlignLambda (AlignVar _ _ LHere))

valid : DependentEndpointFaceEvidence
  {decls = DependentCongruenceWrongAdmission.declarations} {face = the (ScopedFace 1) (SEndpoint FZ False)}
  (CommonLeft {i = Var FZ} CommonDeclaredHere Refl)
  (HOPAt [] [LBool] LBool 1 LHere (Var FZ))
  (HOPOrdinary [] [LBool] LBool 1 DependentCongruenceWrongAdmission.boolDomain)
  DependentCongruenceWrongAdmission.paths DependentCongruenceWrongAdmission.admissible
valid = DepEndpointLeft LHere (Var FZ) DependentCongruenceWrongAdmission.boolDomain CommonDeclaredHere Refl
  DependentCongruenceWrongAdmission.paths DependentCongruenceWrongAdmission.admissible (\env, valuation, holds => DependentCongruenceWrongAdmission.boolAlignment)

bad : DependentEndpointFaceEvidence
  {decls = DependentCongruenceWrongAdmission.declarations} {face = the (ScopedFace 1) (SEndpoint FZ False)}
  (CommonLeft {i = Var FZ} CommonDeclaredHere Refl)
  (HOPAt [] [LBool] LBool 1 LHere (Var FZ))
  (HOPOrdinary [] [LBool] LBool 1 DependentCongruenceWrongAdmission.boolDomain)
  DependentCongruenceWrongAdmission.paths DependentCongruenceWrongAdmission.otherAdmissible
bad = DepEndpointAlign (AlignPathAt [] [LBool] LBool 1 LHere (Var FZ)) DependentCongruenceWrongAdmission.valid (AlignPathOrdinary DependentCongruenceWrongAdmission.boolAlignment)
