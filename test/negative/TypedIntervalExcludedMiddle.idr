module TypedIntervalExcludedMiddle
import Data.Fin
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
%default total

bad : IntervalEquivalent {n = 2} STop
  (Meet (Var FZ) (Join (Var (FS FZ)) (Reverse (Var (FS FZ))))) (Var FZ)
bad = IMeetRightOne Refl
