module ReusablePathMismatch
import Data.Fin
import Fibril.Cubical.Logical.Telescope
import Fibril.Cubical.Logical.ReusablePath

bad : CheckedPath Empty (Tvar FZ) (Tvar FZ) (Tvar FZ) ->
      CheckedPath Empty (Tvar FZ) (Tvar FZ) (Tvar (FS FZ))
bad x = x
