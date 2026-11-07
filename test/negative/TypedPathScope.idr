module TypedPathScope
import Data.Fin
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Cubical.Logical.TypedPath
%default total
bad : HasType {m = 0} {n = 0} (Variable FZ) Universe
bad = BaseVar FZ
