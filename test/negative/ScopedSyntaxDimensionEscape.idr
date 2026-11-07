module ScopedSyntaxDimensionEscape

import Data.Fin
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

bad : Expr 1 0
bad = Apply (Variable FZ) (Var FZ)
