module CommonAdmissionWrongContext

import Data.Vect
import Data.Fin
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.CommonAdmission

bad : AdmittedTerm [LBool] (AVar FZ) LBool -> CommonHasType [LUnit] (CVar FZ) LBool
bad evidence = termTyping evidence
