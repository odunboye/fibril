module ShadowCommonWrongType
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon

bad : CommonHasType [] (CBool True) LUnit
bad = CBoolType
