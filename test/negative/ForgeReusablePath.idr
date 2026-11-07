module ForgeReusablePath
import Data.Fin
import Fibril.Cubical.Logical.Telescope
import Fibril.Cubical.Logical.ReusablePath

bad : CheckedPath Empty (Tvar FZ) (Tvar FZ) (Tvar FZ)
bad = MkCheckedPath
