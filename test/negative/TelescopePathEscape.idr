module TelescopePathEscape
import Data.Fin
import Fibril.Cubical.Logical.Telescope
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
bad : Term 1 0 0
bad = Tapp FZ Zero
