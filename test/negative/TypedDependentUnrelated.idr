module TypedDependentUnrelated
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
%default total
bad : NeutralEqual {n = 0} {m = 2} {k = 0} [] STop
  (NAbstract (NBase FZ)) (NAbstract (NBase (FS FZ)))
  (NPathType NType (NBase FZ) (NBase FZ))
bad = NPathPAbstractCong
  (NIntro NBaseForm (NBaseVar FZ) (NBaseVar FZ) (NBaseVar FZ) (NRefl (NBaseVar FZ)) (NRefl (NBaseVar FZ)))
  (NIntro NBaseForm (NBaseVar (FS FZ)) (NBaseVar (FS FZ)) (NBaseVar (FS FZ)) (NRefl (NBaseVar (FS FZ))) (NRefl (NBaseVar (FS FZ))))
  (NRefl (NBaseVar FZ))
