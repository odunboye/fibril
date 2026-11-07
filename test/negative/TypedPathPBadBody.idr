module TypedPathPBadBody
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
%default total
family : NeutralTypeFormed {n = 1} [PathBetween FZ (FS FZ)] STop
  (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
family = NPathForm NBaseForm (NElim (NPathVar FZ) (Var FZ)) (NElim (NPathVar FZ) (Var FZ))

leftEnd : NeutralHasType {n = 0} [PathBetween FZ (FS FZ)] STop
  (NAbstract (NApply (NPath FZ) Zero))
  (NPathType NType (NApply (NPath FZ) Zero) (NApply (NPath FZ) Zero))
leftEnd = NIntro NBaseForm (NElim (NPathVar FZ) Zero) (NElim (NPathVar FZ) Zero)
  (NElim (NPathVar FZ) Zero) (NRefl (NElim (NPathVar FZ) Zero)) (NRefl (NElim (NPathVar FZ) Zero))

rightEnd : NeutralHasType {n = 0} [PathBetween FZ (FS FZ)] STop
  (NAbstract (NApply (NPath FZ) One))
  (NPathType NType (NApply (NPath FZ) One) (NApply (NPath FZ) One))
rightEnd = NIntro NBaseForm (NElim (NPathVar FZ) One) (NElim (NPathVar FZ) One)
  (NElim (NPathVar FZ) One) (NRefl (NElim (NPathVar FZ) One)) (NRefl (NElim (NPathVar FZ) One))

bad : NeutralHasType {n = 0} [PathBetween FZ (FS FZ)] STop
  (NAbstract (NBase FZ))
  (NPathType (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
    (NAbstract (NApply (NPath FZ) Zero)) (NAbstract (NApply (NPath FZ) One)))
bad = NPathPIntro family leftEnd rightEnd (NBaseVar FZ)
  (NRefl (NBaseVar FZ)) (NRefl (NBaseVar FZ))
