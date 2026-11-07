module HigherOrderPathWrongDimension
import Data.Vect
import Fibril.Cubical.Logical.ShadowTypedBridge


import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.Shadow
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

import Data.Fin

bad : HigherOrderPathTerm [] [LBool] LBool 1 (CPAtType {i = Var FZ} LHere)
bad = HOPAt [] [LBool] LBool 1 LHere (Var (FS FZ))
