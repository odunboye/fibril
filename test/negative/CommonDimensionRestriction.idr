module CommonDimensionRestriction
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

import CommonDimensionFixture

%default total

original : CommonFaceEqual CommonDimensionFixture.declarations (the (ScopedFace 1) SBottom)
  (CPOrdinary (CBool True)) (CPOrdinary (CBool True)) LBool
original = CommonRestrict {source = SEndpoint FZ False} (CommonRefl (CPOrdinaryType CBoolType)) Refl

bad : CommonDimensionEvidence (the (Fin 1 -> ScopedInterval 1) Var) STop CommonDimensionRestriction.original
bad = CommonDimRestrict (CommonDimRefl (CPOrdinaryType CBoolType)) Refl
