module HigherOrderDimensionWrongIndex

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

original : HigherOrderPathTerm [] [LBool] LBool 1 (CPAtType {i = Var FZ} LHere)
original = HOPAt [] [LBool] LBool 1 LHere (Var FZ)

-- The mapped witness is indexed by FS FZ, not the newly introduced FZ.
bad : HigherOrderPathWitness [] [LBool] LBool 2 (CPAt FZ (Var FZ))
bad = mapHigherOrderPathDimensions (Var . FS) HigherOrderDimensionWrongIndex.original
