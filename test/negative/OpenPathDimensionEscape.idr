module OpenPathDimensionEscape
import Data.Fin
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

bad : OpenTerm 1 0
bad = At (Var FZ)
