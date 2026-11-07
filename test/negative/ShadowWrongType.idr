module ShadowWrongType
import Data.Vect

import Fibril.Cubical.Logical.Shadow

bad : LogicalTerm [] LBool
bad = LUnitValue
