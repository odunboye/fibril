module TypedIntervalWrongPath
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
%default total
bad : NeutralEqual {n = 1} {m = 2} {k = 2}
  [PathBetween FZ FZ, PathBetween FZ FZ] STop
  (NApply (NPath FZ) (Meet (Var FZ) One))
  (NApply (NPath (FS FZ)) (Var FZ)) NType
bad = NIntervalApplyCong (NPathVar FZ) (IMeetRightOne Refl)
