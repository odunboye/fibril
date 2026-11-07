module CommonDimensionWrongDerivation
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

equivalent : CommonFaceEqual CommonDimensionFixture.declarations (the (ScopedFace 1) (SEndpoint FZ False))
  (CPAt FZ (Var FZ)) (CPOrdinary (CBool True)) LBool
equivalent = CommonSym (CommonSym CommonDimensionFixture.source)

bad : CommonDimensionEvidence CommonDimensionFixture.first
  (the (ScopedFace 2) (SEndpoint FZ False)) CommonDimensionWrongDerivation.equivalent
bad = CommonDimensionFixture.firstEvidence
