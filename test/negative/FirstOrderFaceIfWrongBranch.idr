module FirstOrderFaceIfWrongBranch

import Data.Vect
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon

bad : FirstOrderFaceEqual
  (the (CommonFaceEqual CommonNoPaths (the (ScopedFace 0) STop)
    (CPIf (CPOrdinary (CBool True)) (CPOrdinary (CBool True)) (CPOrdinary (CBool False)))
    (CPIf (CPOrdinary (CBool True)) (CPOrdinary (CBool True)) (CPOrdinary (CBool False))) LBool)
    (CommonIfEqual (CommonRefl (CPOrdinaryType CBoolType)) (CommonRefl (CPOrdinaryType CBoolType)) (CommonRefl (CPOrdinaryType CBoolType))))
  (FOPathIf (FOOrdinary (FOBool True)) (FOOrdinary (FOBool True)) (FOOrdinary (FOBool False)))
  (FOPathIf (FOOrdinary (FOBool True)) (FOOrdinary (FOBool True)) (FOOrdinary (FOBool False)))
bad = FOFaceIf (FOOrdinary (FOBool True)) (FOOrdinary (FOBool True))
  (FOOrdinary (FOBool True)) (FOOrdinary (FOBool True)) (FOOrdinary (FOBool False)) (FOOrdinary (FOBool False))
  (FOFaceRefl (FOOrdinary (FOBool True))) (FOFaceRefl (FOOrdinary (FOBool False))) (FOFaceRefl (FOOrdinary (FOBool False)))
