module ForgeContextAbstraction

import Data.Fin
import Data.Vect

import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath


bad : CheckedContextAbstraction [] (Variable FZ) FZ FZ
bad = MkCheckedContextAbstraction
