module FirstOrderCoherenceWrongTerm

import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon

bad : interpretFirstOrderTerm (FOBool True) FONil = interpretFirstOrderTerm (FOBool False) FONil
bad = firstOrderTermCoherent (FOBool True) (FOBool False) FONil
