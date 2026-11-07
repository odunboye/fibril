module SquareApplicationMismatch
import Data.Fin
import Fibril.Cubical.Logical.Telescope
import Fibril.Cubical.Logical.Square
import Fibril.Cubical.Logical.ReusablePath
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Interval


bad : CheckedSquare {m=2, k=0, n=0} Empty (Tvar FZ) (Tvar FZ) (Tvar FZ) (Tvar FZ) (Tvar FZ) ->
      Either Result (CheckedPath Empty (Tvar FZ) (Tvar (FS FZ)) (Tvar FZ))
bad sq = applySquare 32 FixI sq Zero
