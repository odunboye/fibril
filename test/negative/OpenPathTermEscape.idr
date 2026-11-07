module OpenPathTermEscape
import Data.Fin
import Fibril.Cubical.Logical.OpenPath
bad : OpenTerm 0 0
bad = AVar FZ
