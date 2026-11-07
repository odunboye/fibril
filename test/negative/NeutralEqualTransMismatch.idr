module NeutralEqualTransMismatch
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

ctx : PathContext 2 1
ctx = [PathBetween FZ (FS FZ)]
first : NeutralEqual NeutralEqualTransMismatch.ctx (the (ScopedFace 1) (SEndpoint FZ False))
  (NApply (NPath FZ) (Var FZ)) (NBase FZ) NType
first = NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl
second : NeutralEqual NeutralEqualTransMismatch.ctx (the (ScopedFace 1) (SEndpoint FZ False))
  (NBase (FS FZ)) (NBase (FS FZ)) NType
second = NRefl (NBaseVar (FS FZ))
bad : NeutralEqual NeutralEqualTransMismatch.ctx (the (ScopedFace 1) (SEndpoint FZ False))
  (NApply (NPath FZ) (Var FZ)) (NBase (FS FZ)) NType
bad = NTrans NeutralEqualTransMismatch.first NeutralEqualTransMismatch.second
