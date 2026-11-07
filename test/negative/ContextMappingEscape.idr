module ContextMappingEscape

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.PathContext

bad : ContextMapping 1 0 0 0
bad = MapContext [FZ] []
