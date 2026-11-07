module FirstOrderFaceFalseHolds

import Data.Vect
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon

bad : faceAtVal (\_ => (True, True)) (the (ScopedFace 1) (SEndpoint FZ False)) = True
bad = Refl
