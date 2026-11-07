module TypedPathPScope
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath

import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
%default total
bad : NeutralTypeFormed {n = 0} [PathBetween FZ (FS FZ)] STop
  (NPathType (NPathType NType (NBase FZ) (NApply (NPath FZ) (Var (FS FZ)))) (NPath FZ) (NPath FZ))
bad = NBaseForm
