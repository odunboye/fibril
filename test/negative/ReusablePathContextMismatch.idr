module ReusablePathContextMismatch
import Data.Fin
import Fibril.Cubical.Logical.Telescope
import Fibril.Cubical.Logical.ReusablePath

bad : CheckedPath (Extend Empty (Tvar FZ) (Tvar FZ)) (Tvar FZ) (Tvar FZ) (Tvar FZ) ->
      CheckedPath (Extend Empty (Tvar FZ) (Tvar (FS FZ))) (Tvar FZ) (Tvar FZ) (Tvar FZ)
bad x = x
