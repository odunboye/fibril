module DependentFaceWrongDerivation

import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Foundation.DeMorgan.Scope

witness : HigherOrderPathTerm [] [] LBool 0 (CPOrdinaryType (CBoolType {b = True}))
witness = HOPOrdinary [] [] LBool 0 (HOBool [] True)

evidence : DependentFaceEvidence {decls = CommonNoPaths} {face = the (ScopedFace 0) STop}
  (CommonRefl (CPOrdinaryType (CBoolType {b = True})))
  DependentFaceWrongDerivation.witness DependentFaceWrongDerivation.witness
evidence = DepFaceRefl (AlignPathOrdinary (AlignBool [] True))

bad : DependentFaceEvidence {decls = CommonNoPaths} {face = the (ScopedFace 0) STop}
  (CommonSym (CommonRefl (CPOrdinaryType (CBoolType {b = True}))))
  DependentFaceWrongDerivation.witness DependentFaceWrongDerivation.witness
bad = DependentFaceWrongDerivation.evidence
