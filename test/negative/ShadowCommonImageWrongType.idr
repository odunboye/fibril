module ShadowCommonImageWrongType
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon

image : Fin 1 -> CommonTerm 0
image FZ = CUnit

bad : CommonSubstitutionTyped [LBool] [] ShadowCommonImageWrongType.image
bad LHere = CUnitType
