module ForgeSquare
import Data.Fin
import Fibril.Cubical.Logical.Telescope
import Fibril.Cubical.Logical.Square

bad : CheckedSquare Empty (Tvar FZ) (Tvar FZ) (Tvar FZ) (Tvar FZ) (Tvar FZ)
bad = MkCheckedSquare
