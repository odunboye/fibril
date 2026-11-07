module ShadowCommonSubstitutionWrongScope

import Data.Fin
import Fibril.Cubical.Logical.ShadowCommon

%default total

bad : CommonTerm 0
bad = substituteCommon (\i => CVar i) (the (CommonTerm 1) (CVar FZ))
