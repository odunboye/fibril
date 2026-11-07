module HigherOrderWrongContext
import Data.Vect
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Cubical.Logical.Shadow
%default total
bad : HigherOrderTerm [LBool, LUnit] LBool (CVariable LHere)
bad = HOVar [LBool, LBool] LBool LHere
