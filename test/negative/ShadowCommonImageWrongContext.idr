module ShadowCommonImageWrongContext
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon

image : Fin 1 -> CommonTerm 1
image FZ = CVar FZ

bad : CommonSubstitutionTyped [LBool] [LUnit] ShadowCommonImageWrongContext.image
bad LHere = CVariable LHere
