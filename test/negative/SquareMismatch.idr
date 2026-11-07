module SquareMismatch
import Data.Fin
import Fibril.Cubical.Logical.Telescope
import Fibril.Cubical.Logical.Square

bad : CheckedSquare Empty (Tvar FZ) (Tvar FZ) (Tvar FZ) (Tvar FZ) (Tvar FZ) ->
      CheckedSquare Empty (Tvar FZ) (Tvar (FS FZ)) (Tvar FZ) (Tvar FZ) (Tvar FZ)
bad x = x
