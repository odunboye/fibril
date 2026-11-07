module ShadowCommonRelationWrongImage
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon

logical : LogicalSubstitution [LBool] []
logical LHere = LBoolean True

wrongImage : Fin 1 -> CommonTerm 0
wrongImage FZ = CUnit

bad : CommonSubstitutionRelation ShadowCommonRelationWrongImage.logical ShadowCommonRelationWrongImage.wrongImage
bad LHere = Refl
