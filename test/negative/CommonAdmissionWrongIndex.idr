module CommonAdmissionWrongIndex

import Data.Fin
import Fibril.Cubical.Logical.CommonAdmission

bad : AdmissionTerm 1
bad = AVar (FS FZ)
