module TypedPathAnnotation
import Data.Fin
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Cubical.Logical.TypedPath
%default total
bad : HasType {m = 1} {n = 0} (Variable FZ) (Path Universe (Variable FZ) (Variable FZ))
bad = BaseVar FZ
