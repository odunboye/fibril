module HigherOrderWrongType
import Data.Vect
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.Shadow
%default total
bad : HigherOrderTerm [] LUnit CUnitType
bad = HOBool [] True
