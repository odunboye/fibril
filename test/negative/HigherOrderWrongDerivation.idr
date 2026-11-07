module HigherOrderWrongDerivation
import Data.Vect
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.Shadow
%default total
bad : HigherOrderTerm [] LBool (CBoolType {b = True})
bad = HOBool [] False
