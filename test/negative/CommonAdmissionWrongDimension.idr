module CommonAdmissionWrongDimension

import Data.Fin
import Fibril.Cubical.Logical.CommonAdmission
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

bad : AdmissionPathTerm 0 1 1
bad = APAt FZ (Var (FS FZ))
