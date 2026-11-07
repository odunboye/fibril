module HigherOrderPathAlignmentInterval
import Data.Vect
import Data.Fin
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

atZero : HigherOrderPathTerm [] [LBool] LBool 1 (CPAtType {i = Zero} LHere)
atZero = HOPAt [] [LBool] LBool 1 LHere Zero

atVariable : HigherOrderPathTerm [] [LBool] LBool 1 (CPAtType {i = Var FZ} LHere)
atVariable = HOPAt [] [LBool] LBool 1 LHere (Var FZ)

bad : HigherOrderPathAlignment HigherOrderPathAlignmentInterval.atZero HigherOrderPathAlignmentInterval.atZero
bad = the (HigherOrderPathAlignment HigherOrderPathAlignmentInterval.atVariable HigherOrderPathAlignmentInterval.atVariable)
  (AlignPathAt [] [LBool] LBool 1 LHere (Var FZ))
