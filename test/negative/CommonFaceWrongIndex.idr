module CommonFaceWrongIndex
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge

import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Foundation.DeMorgan.Face

import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

bad : CommonFaceEqual (CommonDeclarePath (CBool True) (CBool False) CBoolType CBoolType
  (CommonDeclarePath (CBool False) (CBool True) CBoolType CBoolType CommonNoPaths))
  (the (ScopedFace 1) (SEndpoint FZ False)) (CPAt (FS FZ) (Var FZ)) (CPOrdinary (CBool True)) LBool
bad = CommonLeft CommonDeclaredHere Refl
