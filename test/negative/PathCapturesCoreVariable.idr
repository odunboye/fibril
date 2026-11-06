-- A closed path cannot embed a computational variable.
module PathCapturesCoreVariable

import Data.Fin
import Fibril.Core.Term
import Fibril.Foundation.DeMorgan.ClosedCorePath

bad : CorePathExpr 0
bad = CoreAbstract (CoreTerm (Variable FZ))
