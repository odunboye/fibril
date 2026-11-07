module DependentEndpointWrongAlignment

import Fibril.Cubical.Logical.OpenPath
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

endpoint : DependentEndpointAtFace [] {paths = [LBool]} LHere
  (CApp (CLam (CBool True)) (CLam (CVar FZ))) (commonConstant True, ()) () (False, False)
endpoint = DependentAtFace DependentEndpointWrongAlignment.boolDomain Refl

selectedEndpoint : DependentEndpointAtFace [] {paths = [LBool]} LHere
  (CApp (CLam (CBool True)) (CLam (CVar FZ))) (commonConstant True, ()) () (False, False)
selectedEndpoint = DependentAtFace DependentEndpointWrongAlignment.unitDomain Refl

bad : DependentEndpointAlignment DependentEndpointWrongAlignment.unitDomain DependentEndpointWrongAlignment.endpoint
bad = AlignApplication (AlignLambda (AlignBool _ True)) (AlignLambda (AlignVar _ _ LHere))
