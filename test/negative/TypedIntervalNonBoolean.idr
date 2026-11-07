module TypedIntervalNonBoolean
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
%default total
bad : IntervalEquivalent {n = 1} STop (Meet (Var FZ) (Reverse (Var FZ))) Zero
bad = IMeetRightOne Refl
