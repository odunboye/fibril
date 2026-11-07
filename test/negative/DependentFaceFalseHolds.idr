module DependentFaceFalseHolds

import Data.Vect
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Foundation.DeMorgan.Scope

witness : HigherOrderPathTerm [] [] LBool 1 (CPOrdinaryType (CBoolType {b = True}))
witness = HOPOrdinary [] [] LBool 1 (HOBool [] True)

evidence : DependentFaceEvidence {decls = CommonNoPaths} {face = the (ScopedFace 1) (SEndpoint FZ False)}
  (CommonRefl (CPOrdinaryType (CBoolType {b = True})))
  DependentFaceFalseHolds.witness DependentFaceFalseHolds.witness
evidence = DepFaceRefl (AlignPathOrdinary (AlignBool [] True))

bad : related (commonTypeSetoid LBool)
  (applyMorphism (dependentPathSemantics DependentFaceFalseHolds.witness (\_ => (True, True))) ((), ()))
  (applyMorphism (dependentPathSemantics DependentFaceFalseHolds.witness (\_ => (True, True))) ((), ()))
bad = dependentFaceEvidenceSound DependentFaceFalseHolds.evidence () () DependentAdmissibleNil (\_ => (True, True)) Refl
