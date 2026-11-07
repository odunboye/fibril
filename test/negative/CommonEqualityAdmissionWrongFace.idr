module CommonEqualityAdmissionWrongFace

import Data.Vect
import Data.Fin
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.CommonAdmission
import Fibril.Foundation.DeMorgan.Scope

bad : AdmittedEquality [] [] CommonNoPaths (the (ScopedFace 0) STop)
  (APOrdinary (ABool True)) (APOrdinary (ABool True)) LBool ->
  CommonFaceEqual {ctx = []} {paths = []} CommonNoPaths (the (ScopedFace 0) SBottom)
    (CPOrdinary (CBool True)) (CPOrdinary (CBool True)) LBool
bad e = faceEquality e
