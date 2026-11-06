-- A closed path application cannot reference an undeclared dimension.
module PathEscapesDimension

import Data.Fin
import Fibril.Core.Term
import Fibril.Foundation.DeMorgan.ClosedCorePath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

bad : CorePathExpr 0
bad = CoreApply (CoreAbstract (CoreTerm BoolTrue)) (Var FZ)
