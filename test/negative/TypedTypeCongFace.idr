module TypedTypeCongFace
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath

import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
%default total
falseEquality : NeutralTypeEqual {n = 1} {m = 1} {k = 0} [] SBottom NType NType
falseEquality = NTypeRefl NBaseForm
bad : NeutralTypeEqual {n = 1} {m = 1} {k = 0} [] STop NType NType
bad = falseEquality
