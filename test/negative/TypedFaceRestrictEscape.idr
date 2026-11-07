module TypedFaceRestrictEscape
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Scope
%default total
bad : NeutralHasType {n = 1} {m = 1} {k = 0} [] STop (NBase FZ) NType
bad = NFaceRestrict (the (NeutralHasType [] SBottom (NBase FZ) NType) (NBaseVar FZ)) Refl
