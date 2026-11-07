module HigherOrderPathAlignmentDomain
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge

boolDomain : HigherOrderPathTerm [] [] LBool 0
  (CPAppType {a = LArrow LBool LBool} (CPLamType (CPOrdinaryType (CBoolType {b = True}))) (CPLamType (CPOrdinaryType (CVariable LHere))))
boolDomain = HOPApplication [] [] (LArrow LBool LBool) LBool 0
  (HOPLambda [] [] (LArrow LBool LBool) LBool 0 (HOPOrdinary [LArrow LBool LBool] [] LBool 0 (HOBool [LArrow LBool LBool] True)))
  (HOPLambda [] [] LBool LBool 0 (HOPOrdinary [LBool] [] LBool 0 (HOVar [LBool] LBool LHere)))

unitDomain : HigherOrderPathTerm [] [] LBool 0
  (CPAppType {a = LArrow LUnit LUnit} (CPLamType (CPOrdinaryType (CBoolType {b = True}))) (CPLamType (CPOrdinaryType (CVariable LHere))))
unitDomain = HOPApplication [] [] (LArrow LUnit LUnit) LBool 0
  (HOPLambda [] [] (LArrow LUnit LUnit) LBool 0 (HOPOrdinary [LArrow LUnit LUnit] [] LBool 0 (HOBool [LArrow LUnit LUnit] True)))
  (HOPLambda [] [] LUnit LUnit 0 (HOPOrdinary [LUnit] [] LUnit 0 (HOVar [LUnit] LUnit LHere)))

bad : HigherOrderPathAlignment HigherOrderPathAlignmentDomain.boolDomain HigherOrderPathAlignmentDomain.unitDomain
bad = AlignPathApplication (AlignPathLambda (AlignPathOrdinary (AlignBool _ True)))
  (AlignPathLambda (AlignPathOrdinary (AlignVar _ _ LHere)))
