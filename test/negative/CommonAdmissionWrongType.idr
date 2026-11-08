module CommonAdmissionWrongType

import Data.Vect
import Data.Fin
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.CommonAdmission

bad : AdmittedTerm [LBool] (AVar FZ) LBool -> CommonHasType [LBool] (CVar FZ) LUnit
bad evidence = termTyping evidence
