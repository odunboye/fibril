module HigherOrderAlignmentAmbiguous

import Data.Vect
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

bad : HigherOrderAlignment HigherOrderAlignmentAmbiguous.boolDomain HigherOrderAlignmentAmbiguous.unitDomain
bad = AlignApplication (AlignLambda (AlignBool _ True)) (AlignLambda (AlignVar _ _ LHere))
