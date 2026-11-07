module HigherOrderPathAlignmentIndex
import Data.Vect
import Data.Fin
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

first : HigherOrderPathTerm [] [LBool, LBool] LBool 1 (CPAtType {i = Var FZ} LHere)
first = HOPAt [] [LBool, LBool] LBool 1 LHere (Var FZ)

second : HigherOrderPathTerm [] [LBool, LBool] LBool 1 (CPAtType {i = Var FZ} (LThere LHere))
second = HOPAt [] [LBool, LBool] LBool 1 (LThere LHere) (Var FZ)

bad : HigherOrderPathAlignment HigherOrderPathAlignmentIndex.first HigherOrderPathAlignmentIndex.first
bad = the (HigherOrderPathAlignment HigherOrderPathAlignmentIndex.second HigherOrderPathAlignmentIndex.second)
  (AlignPathAt [] [LBool, LBool] LBool 1 (LThere LHere) (Var FZ))
