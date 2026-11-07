module TypedEqualConvertFace
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Scope
%default total
bottom : NeutralEqual {n = 1} {m = 1} {k = 0} [] SBottom (NBase FZ) (NBase FZ) NType
bottom = NRefl (NBaseVar FZ)
bad : NeutralEqual {n = 1} {m = 1} {k = 0} [] STop (NBase FZ) (NBase FZ) NType
bad = NEqualConvert bottom (NTypeRefl NBaseForm) (NBaseVar FZ) (NBaseVar FZ)
