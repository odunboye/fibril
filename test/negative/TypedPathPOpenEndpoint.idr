module TypedPathPOpenEndpoint
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
%default total

-- This is an ordinary hypothetical path-over judgment, not an axiom that such
-- a derivation exists in this restricted calculus. The endpoint derivation is
-- concrete and typed at the zero-substituted family only.
bad : NeutralHasType {n = 1} [PathBetween FZ (FS FZ)] (SEndpoint FZ False) p
    (NPathType
      (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
      (NAbstract (NApply (NPath FZ) Zero))
      (NAbstract (NApply (NPath FZ) One))) ->
  NeutralEqual [PathBetween FZ (FS FZ)] (SEndpoint FZ False)
    (NApply p (Var FZ)) (NAbstract (NApply (NPath FZ) Zero))
    (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
bad h = NPathPEndpointLeft h
  (NIntro NBaseForm (NElim (NPathVar FZ) Zero) (NElim (NPathVar FZ) Zero)
    (NElim (NPathVar FZ) Zero) (NRefl (NElim (NPathVar FZ) Zero))
    (NRefl (NElim (NPathVar FZ) Zero))) Refl
