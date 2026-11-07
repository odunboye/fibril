module TypedNeutralWrongEndpoint
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
%default total

bad : NeutralEqual {n = 1} [PathBetween FZ (FS FZ)] (SEndpoint FZ False)
  (NApply (NPath FZ) (Var FZ)) (NBase (FS FZ)) NType
bad = NEndpointLeft (NPathVar FZ) (NBaseVar (FS FZ)) Refl
