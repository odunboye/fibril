module ContextDimensionEscape
import Fibril.Foundation.DeMorgan.Interval

import Data.Fin

import Fibril.Cubical.Logical.PathContext
import Fibril.Foundation.DeMorgan.Scope
bad : ContextTerm 1 1 0
bad = ApplyPath FZ (Var FZ)
