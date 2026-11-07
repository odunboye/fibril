module CommonFaceWrongType
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Foundation.DeMorgan.Scope

bad : CommonFaceEqual CommonNoPaths (the (ScopedFace 0) STop)
  (CPOrdinary (CBool True)) (CPOrdinary (CBool True)) LUnit
bad = CommonRefl (CPOrdinaryType CBoolType)
