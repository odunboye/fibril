module TelescopeCycle
import Data.Fin
import Fibril.Cubical.Logical.Telescope
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
bad : Telescope 1 1
bad = Extend Empty (Tapp FZ Zero) (Tvar FZ)
