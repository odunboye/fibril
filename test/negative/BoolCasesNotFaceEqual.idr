module BoolCasesNotFaceEqual

import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Cubical.Source.BoolCases

agreement : BoolAgreement Input (Conditional Input (Literal True) (Literal False))
agreement = ByBoolCases Refl Refl

bad : CommonFaceEqual (the (CommonDeclarations [] []) CommonNoPaths) (the (ScopedFace 0) STop)
  (CPOrdinary (CBool True)) (CPOrdinary (CBool True)) LBool
bad = agreement
