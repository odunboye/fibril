module DependentEndpointFaceWrongTrans
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Foundation.DeMorgan.Scope

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


boolEvidence : DependentFaceEvidence {decls = CommonNoPaths} {face = the (ScopedFace 0) STop}
  (CommonRefl (CPAppType {a = LArrow LBool LBool} (CPLamType (CPOrdinaryType (CBoolType {b = True}))) (CPLamType (CPOrdinaryType (CVariable LHere)))))
  DependentEndpointFaceWrongTrans.boolDomain DependentEndpointFaceWrongTrans.boolDomain
boolEvidence = DepFaceRefl (AlignPathApplication (AlignPathLambda (AlignPathOrdinary (AlignBool _ True)))
  (AlignPathLambda (AlignPathOrdinary (AlignVar _ _ LHere))))

unitEvidence : DependentFaceEvidence {decls = CommonNoPaths} {face = the (ScopedFace 0) STop}
  (CommonRefl (CPAppType {a = LArrow LUnit LUnit} (CPLamType (CPOrdinaryType (CBoolType {b = True}))) (CPLamType (CPOrdinaryType (CVariable LHere)))))
  DependentEndpointFaceWrongTrans.unitDomain DependentEndpointFaceWrongTrans.unitDomain
unitEvidence = DepFaceRefl (AlignPathApplication (AlignPathLambda (AlignPathOrdinary (AlignBool _ True)))
  (AlignPathLambda (AlignPathOrdinary (AlignVar _ _ LHere))))

boolAlignment : HigherOrderPathAlignment DependentEndpointFaceWrongTrans.boolDomain DependentEndpointFaceWrongTrans.boolDomain
boolAlignment = AlignPathApplication (AlignPathLambda (AlignPathOrdinary (AlignBool _ True)))
  (AlignPathLambda (AlignPathOrdinary (AlignVar _ _ LHere)))

boolEndpointEvidence : DependentEndpointFaceEvidence
  {decls = CommonNoPaths} {face = the (ScopedFace 0) STop}
  (CommonRefl (CPAppType {a = LArrow LBool LBool} (CPLamType (CPOrdinaryType (CBoolType {b = True}))) (CPLamType (CPOrdinaryType (CVariable LHere)))))
  DependentEndpointFaceWrongTrans.boolDomain DependentEndpointFaceWrongTrans.boolDomain () DependentAdmissibleNil
boolEndpointEvidence = DepEndpointStructural DependentEndpointFaceWrongTrans.boolEvidence

unitEndpointEvidence : DependentEndpointFaceEvidence
  {decls = CommonNoPaths} {face = the (ScopedFace 0) STop}
  (CommonRefl (CPAppType {a = LArrow LUnit LUnit} (CPLamType (CPOrdinaryType (CBoolType {b = True}))) (CPLamType (CPOrdinaryType (CVariable LHere)))))
  DependentEndpointFaceWrongTrans.unitDomain DependentEndpointFaceWrongTrans.unitDomain () DependentAdmissibleNil
unitEndpointEvidence = DepEndpointStructural DependentEndpointFaceWrongTrans.unitEvidence

bad : DependentEndpointFaceEvidence {decls = CommonNoPaths} {face = the (ScopedFace 0) STop}
  (CommonTrans
    (CommonRefl (CPAppType {a = LArrow LBool LBool} (CPLamType (CPOrdinaryType (CBoolType {b = True}))) (CPLamType (CPOrdinaryType (CVariable LHere)))))
    (CommonRefl (CPAppType {a = LArrow LUnit LUnit} (CPLamType (CPOrdinaryType (CBoolType {b = True}))) (CPLamType (CPOrdinaryType (CVariable LHere))))))
  DependentEndpointFaceWrongTrans.boolDomain DependentEndpointFaceWrongTrans.unitDomain () DependentAdmissibleNil
bad = DepEndpointTrans DependentEndpointFaceWrongTrans.boolEndpointEvidence DependentEndpointFaceWrongTrans.boolAlignment DependentEndpointFaceWrongTrans.unitEndpointEvidence
