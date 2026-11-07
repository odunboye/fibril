module TypedNeutralFalseFace
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
%default total
bad : NeutralEqual {n = 1} [PathBetween FZ (FS FZ)] STop
  (NApply (NPath FZ) (Var FZ)) (NBase FZ) NType
bad = NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl
