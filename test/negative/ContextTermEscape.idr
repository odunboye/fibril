module ContextTermEscape

import Data.Fin
import Fibril.Cubical.Logical.PathContext

bad : ContextTerm 0 1 0
bad = Variable FZ
