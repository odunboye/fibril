module TypedPathPBadFamily
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath

import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Scope
%default total
bad : NeutralTypeFormed {n = 0} [PathBetween FZ (FS FZ)] STop
  (NPathType (NBase FZ) (NBase FZ) (NBase FZ))
bad = NPathPForm NBaseForm (NBaseVar FZ) (NBaseVar FZ)
