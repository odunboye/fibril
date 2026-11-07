module TypedPathNonDimension
import Data.Fin
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Scope

%default total
bad : HasType {m = 1} {n = 0} (Apply (Variable FZ) True) Universe
bad = BaseVar FZ
