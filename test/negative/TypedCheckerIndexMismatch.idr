module TypedCheckerIndexMismatch

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.TypedPathChecker
import Fibril.Foundation.DeMorgan.Scope

%default total

ctx : PathContext 2 1
ctx = [PathBetween FZ (FS FZ)]

bad : Either CheckError (NeutralHasType {n = 0} TypedCheckerIndexMismatch.ctx STop (NPath FZ)
  (NPathType NType (NBase (FS FZ)) (NBase FZ)))
bad = checkNeutral 32 ctx STop (NPath FZ)
  (NPathType NType (NBase FZ) (NBase (FS FZ)))
