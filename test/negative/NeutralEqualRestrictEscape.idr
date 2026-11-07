module NeutralEqualRestrictEscape
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

ctx : PathContext 2 1
ctx = [PathBetween FZ (FS FZ)]

leftEq : NeutralEqual NeutralEqualRestrictEscape.ctx (the (ScopedFace 1) (SEndpoint FZ False))
  (NApply (NPath FZ) (Var FZ)) (NBase FZ) NType
leftEq = NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl

bad : NeutralEqual NeutralEqualRestrictEscape.ctx (the (ScopedFace 1) STop)
  (NApply (NPath FZ) (Var FZ)) (NBase FZ) NType
bad = NEqualRestrict NeutralEqualRestrictEscape.leftEq Refl
