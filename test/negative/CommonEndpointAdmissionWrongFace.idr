module CommonEndpointAdmissionWrongFace

import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.CommonAdmission
import Fibril.Foundation.DeMorgan.Scope

bad : AdmittedCanonicalEquality (the (AdmittedDeclarations [] ADNil) CheckedNoPaths)
  (the (ScopedFace 0) STop) (APOrdinary (ABool True)) (APOrdinary (ABool True)) LBool ->
  CommonFaceEqual (the (CommonDeclarations [] []) CommonNoPaths) (the (ScopedFace 0) SBottom)
    (CPOrdinary (CBool True)) (CPOrdinary (CBool True)) LBool
bad e = canonicalEquality e
