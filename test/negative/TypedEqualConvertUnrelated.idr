module TypedEqualConvertUnrelated
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Scope
%default total
bad : NeutralEqual {n = 0} {m = 1} {k = 0} [] STop (NBase FZ) (NBase FZ)
  (NPathType NType (NBase FZ) (NBase FZ))
bad = NEqualConvert (NRefl (NBaseVar FZ)) (NTypeRefl NBaseForm) (NBaseVar FZ) (NBaseVar FZ)
