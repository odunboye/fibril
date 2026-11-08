module CommonAdmissionUsesReflection

import Data.Vect
import Data.Fin
import Fibril.Core.Usage
import Fibril.Core.Quantity
import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Quantitative.Usage
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.CommonAdmission

bad : AdmittedTerm [LBool] (AVar FZ) LBool ->
  Uses (the (Term [BoolTy] BoolTy) (Ref Here)) [Erased]
bad evidence = termTyping evidence
