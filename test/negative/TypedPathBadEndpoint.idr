module TypedPathBadEndpoint
import Data.Fin
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Cubical.Logical.TypedPath
%default total
bad : HasType {m = 2} {n = 0} (Abstract (Variable FZ))
  (Path Universe (Variable FZ) (Variable (FS FZ)))
bad = PathIntro Base (BaseVar FZ) (BaseVar (FS FZ)) (BaseVar FZ) Refl Refl
