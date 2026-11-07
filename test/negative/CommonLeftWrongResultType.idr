module CommonLeftWrongResultType
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

bad : CommonFaceEqual CommonDimensionFixture.declarations (the (ScopedFace 0) STop)
  (CPAt FZ Zero) (CPOrdinary (CBool True)) LUnit
bad = CommonLeft CommonDeclaredHere Refl
