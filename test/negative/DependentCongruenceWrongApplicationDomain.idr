module DependentCongruenceWrongApplicationDomain

import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge

import Fibril.Foundation.DeMorgan.Scope

boolIdentity : HigherOrderPathTerm [] [] (LArrow LBool LBool) 0
  (CPLamType (CPOrdinaryType (CVariable LHere)))
boolIdentity = HOPLambda [] [] LBool LBool 0
  (HOPOrdinary [LBool] [] LBool 0 (HOVar [LBool] LBool LHere))

boolArgument : HigherOrderPathTerm [] [] LBool 0 (CPOrdinaryType (CBoolType {b = True}))
boolArgument = HOPOrdinary [] [] LBool 0 (HOBool [] True)

unitArgument : HigherOrderPathTerm [] [] LUnit 0 (CPOrdinaryType CUnitType)
unitArgument = HOPOrdinary [] [] LUnit 0 (HOUnit [])

functionEvidence : DependentEndpointFaceEvidence {decls = CommonNoPaths} {face = the (ScopedFace 0) STop}
  (CommonRefl (CPLamType (CPOrdinaryType (CVariable LHere))))
  DependentCongruenceWrongApplicationDomain.boolIdentity DependentCongruenceWrongApplicationDomain.boolIdentity () DependentAdmissibleNil
functionEvidence = DepEndpointStructural (DepFaceRefl (AlignPathLambda (AlignPathOrdinary (AlignVar [LBool] LBool LHere))))

unitEvidence : DependentEndpointFaceEvidence {decls = CommonNoPaths} {face = the (ScopedFace 0) STop}
  (CommonRefl (CPOrdinaryType CUnitType))
  DependentCongruenceWrongApplicationDomain.unitArgument DependentCongruenceWrongApplicationDomain.unitArgument () DependentAdmissibleNil
unitEvidence = DepEndpointStructural (DepFaceRefl (AlignPathOrdinary (AlignUnit [])))

bad : DependentEndpointFaceEvidence {decls = CommonNoPaths} {face = the (ScopedFace 0) STop}
  (CommonAppEqual (CommonRefl (CPLamType (CPOrdinaryType (CVariable LHere))))
                  (CommonRefl (CPOrdinaryType (CBoolType {b = True}))))
  (HOPApplication [] [] LBool LBool 0 DependentCongruenceWrongApplicationDomain.boolIdentity DependentCongruenceWrongApplicationDomain.boolArgument)
  (HOPApplication [] [] LBool LBool 0 DependentCongruenceWrongApplicationDomain.boolIdentity DependentCongruenceWrongApplicationDomain.boolArgument)
  () DependentAdmissibleNil
bad = DepEndpointApp DependentCongruenceWrongApplicationDomain.functionEvidence DependentCongruenceWrongApplicationDomain.unitEvidence
