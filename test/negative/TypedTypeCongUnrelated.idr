module TypedTypeCongUnrelated
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath

import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
%default total
bad : NeutralTypeEqual {n = 0} {m = 2} {k = 0} [] STop
  (NPathType NType (NBase FZ) (NBase FZ))
  (NPathType NType (NBase FZ) (NBase (FS FZ)))
bad = NPathTypeCong NBaseForm
  (NBaseVar FZ) (NBaseVar FZ) (NBaseVar FZ) (NBaseVar (FS FZ))
  (NRefl (NBaseVar FZ)) (NRefl (NBaseVar FZ))
