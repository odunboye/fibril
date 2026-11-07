module Tests.Cubical.TypedPath

import Data.Fin
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope


%default total

-- All derivations are checked by Idris; neither endpoints nor the path type
-- are trusted annotations. The context is one variable of A.
constant : HasType {m = 1} {n = 0} (Abstract (Variable FZ))
  (Path Universe (Variable FZ) (Variable FZ))
constant = PathIntro Base (BaseVar FZ) (BaseVar FZ) (BaseVar FZ) Refl Refl

application : HasType {m = 1} {n = 0} (Apply (Abstract (Variable FZ)) Zero) Universe
application = PathElim constant Zero

nested : HasType {m = 1} {n = 0} (Abstract (Abstract (Variable FZ)))
  (Path (Path Universe (Variable FZ) (Variable FZ))
    (Abstract (Variable FZ)) (Abstract (Variable FZ)))
nested = PathIntro (PathForm Base (BaseVar FZ) (BaseVar FZ)) constant constant
  (PathIntro Base (BaseVar FZ) (BaseVar FZ) (BaseVar FZ) Refl Refl) Refl Refl

-- The body really depends on the bound dimension. This judgment does not
-- identify the two applications by beta conversion.
varying : HasType {m = 1} {n = 0}
  (Abstract (Apply (Abstract (Variable FZ)) (Var FZ)))
  (Path Universe (Apply (Abstract (Variable FZ)) Zero)
                 (Apply (Abstract (Variable FZ)) One))
varying = PathIntro Base (PathElim constant Zero) (PathElim constant One)
  (PathElim (PathIntro Base (BaseVar FZ) (BaseVar FZ) (BaseVar FZ) Refl Refl) (Var FZ)) Refl Refl
