module CommonEqualityAdmissionWrongType

import Data.Vect
import Data.Fin
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.CommonAdmission
import Fibril.Foundation.DeMorgan.Scope

bad : AdmittedEquality [] [] CommonNoPaths (the (ScopedFace 0) STop)
  (APOrdinary (ABool True)) (APOrdinary (ABool True)) LBool ->
  AdmittedPathTerm [] [] 0 (APOrdinary (ABool True)) LUnit
bad e = equalityLeft e
