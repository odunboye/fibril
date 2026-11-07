module ShadowCommonWrongContext
import Data.Vect
import Data.Fin
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge


bad : CommonHasType [LUnit] (CVar FZ) LBool
bad = CVariable LHere
