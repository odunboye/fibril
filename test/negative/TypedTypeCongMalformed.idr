module TypedTypeCongMalformed
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath

import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
%default total
bad : NeutralTypeEqual {n = 0} {m = 1} {k = 0} [] STop (NBase FZ) (NBase FZ)
bad = NTypeRefl NBaseForm
