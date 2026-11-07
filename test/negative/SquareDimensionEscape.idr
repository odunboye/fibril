module SquareDimensionEscape
import Data.Fin
import Fibril.Cubical.Logical.Telescope
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
bad : Term 1 1 2
bad = Tapp FZ (Var (FS (FS FZ)))
