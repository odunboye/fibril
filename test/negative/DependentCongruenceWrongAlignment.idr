module DependentCongruenceWrongAlignment
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
  DependentCongruenceWrongAlignment.boolDomain DependentCongruenceWrongAlignment.boolDomain
boolEvidence = DepFaceRefl (AlignPathApplication (AlignPathLambda (AlignPathOrdinary (AlignBool _ True)))
  (AlignPathLambda (AlignPathOrdinary (AlignVar _ _ LHere))))

unitEvidence : DependentFaceEvidence {decls = CommonNoPaths} {face = the (ScopedFace 0) STop}
  (CommonRefl (CPAppType {a = LArrow LUnit LUnit} (CPLamType (CPOrdinaryType (CBoolType {b = True}))) (CPLamType (CPOrdinaryType (CVariable LHere)))))
  DependentCongruenceWrongAlignment.unitDomain DependentCongruenceWrongAlignment.unitDomain
unitEvidence = DepFaceRefl (AlignPathApplication (AlignPathLambda (AlignPathOrdinary (AlignBool _ True)))
  (AlignPathLambda (AlignPathOrdinary (AlignVar _ _ LHere))))

boolAlignment : HigherOrderPathAlignment DependentCongruenceWrongAlignment.boolDomain DependentCongruenceWrongAlignment.boolDomain
boolAlignment = AlignPathApplication (AlignPathLambda (AlignPathOrdinary (AlignBool _ True)))
  (AlignPathLambda (AlignPathOrdinary (AlignVar _ _ LHere)))

boolEndpointEvidence : DependentEndpointFaceEvidence
  {decls = CommonNoPaths} {face = the (ScopedFace 0) STop}
  (CommonRefl (CPAppType {a = LArrow LBool LBool} (CPLamType (CPOrdinaryType (CBoolType {b = True}))) (CPLamType (CPOrdinaryType (CVariable LHere)))))
  DependentCongruenceWrongAlignment.boolDomain DependentCongruenceWrongAlignment.boolDomain () DependentAdmissibleNil
boolEndpointEvidence = DepEndpointStructural DependentCongruenceWrongAlignment.boolEvidence

unitEndpointEvidence : DependentEndpointFaceEvidence
  {decls = CommonNoPaths} {face = the (ScopedFace 0) STop}
  (CommonRefl (CPAppType {a = LArrow LUnit LUnit} (CPLamType (CPOrdinaryType (CBoolType {b = True}))) (CPLamType (CPOrdinaryType (CVariable LHere)))))
  DependentCongruenceWrongAlignment.unitDomain DependentCongruenceWrongAlignment.unitDomain () DependentAdmissibleNil
unitEndpointEvidence = DepEndpointStructural DependentCongruenceWrongAlignment.unitEvidence

bad : DependentEndpointFaceEvidence {decls = CommonNoPaths} {face = the (ScopedFace 0) STop}
  (CommonRefl (CPAppType {a = LArrow LBool LBool} (CPLamType (CPOrdinaryType (CBoolType {b = True}))) (CPLamType (CPOrdinaryType (CVariable LHere)))))
  DependentCongruenceWrongAlignment.boolDomain DependentCongruenceWrongAlignment.unitDomain () DependentAdmissibleNil
bad = DepEndpointAlign DependentCongruenceWrongAlignment.boolAlignment DependentCongruenceWrongAlignment.boolEndpointEvidence DependentCongruenceWrongAlignment.boolAlignment
