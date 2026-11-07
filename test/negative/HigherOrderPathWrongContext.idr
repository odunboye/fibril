module HigherOrderPathWrongContext
import Data.Vect
import Fibril.Cubical.Logical.ShadowTypedBridge


import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.Shadow
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope


bad : HigherOrderPathTerm [] [LBool, LUnit] LBool 0 (CPAtType {i = Zero} LHere)
bad = HOPAt [] [LBool, LBool] LBool 0 LHere Zero
