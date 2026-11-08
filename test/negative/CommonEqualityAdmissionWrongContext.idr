module CommonEqualityAdmissionWrongContext

import Data.Vect
import Data.Fin
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.CommonAdmission
import Fibril.Foundation.DeMorgan.Scope

bad : AdmittedEquality [LBool] [] CommonNoPaths (the (ScopedFace 0) STop)
  (APOrdinary (AVar FZ)) (APOrdinary (AVar FZ)) LBool ->
  AdmittedPathTerm [LUnit] [] 0 (APOrdinary (AVar FZ)) LBool
bad e = equalityLeft e
