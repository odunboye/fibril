module DependentCongruenceWrongSubproof
import Data.Vect

import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Foundation.DeMorgan.Scope

w : HigherOrderPathTerm [] [] LBool 0 (CPOrdinaryType (CBoolType {b = True}))
w = HOPOrdinary [] [] LBool 0 (HOBool [] True)

evidence : DependentEndpointFaceEvidence {decls = CommonNoPaths} {face = the (ScopedFace 0) STop}
  (CommonRefl (CPOrdinaryType (CBoolType {b = True}))) DependentCongruenceWrongSubproof.w DependentCongruenceWrongSubproof.w () DependentAdmissibleNil
evidence = DepEndpointStructural (DepFaceRefl (AlignPathOrdinary (AlignBool [] True)))

bad : DependentEndpointFaceEvidence {decls = CommonNoPaths} {face = the (ScopedFace 0) STop}
  (CommonIfEqual (CommonSym (CommonRefl (CPOrdinaryType (CBoolType {b = True}))))
    (CommonRefl (CPOrdinaryType (CBoolType {b = True}))) (CommonRefl (CPOrdinaryType (CBoolType {b = True}))))
  (HOPIf [] [] LBool 0 DependentCongruenceWrongSubproof.w DependentCongruenceWrongSubproof.w DependentCongruenceWrongSubproof.w)
  (HOPIf [] [] LBool 0 DependentCongruenceWrongSubproof.w DependentCongruenceWrongSubproof.w DependentCongruenceWrongSubproof.w) () DependentAdmissibleNil
bad = DepEndpointIf DependentCongruenceWrongSubproof.evidence DependentCongruenceWrongSubproof.evidence DependentCongruenceWrongSubproof.evidence
