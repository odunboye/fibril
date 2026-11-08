module CommonEqualityAdmissionUsesReflection

import Data.Vect
import Data.Fin
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.CommonAdmission
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Core.Quantity
import Fibril.Core.Usage
import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Quantitative.Usage

bad : AdmittedEquality [LBool] [] CommonNoPaths (the (ScopedFace 0) STop)
  (APOrdinary (AVar FZ)) (APOrdinary (AVar FZ)) LBool ->
  Uses (the (Term [BoolTy] BoolTy) (Ref Here)) [Erased]
bad e = faceEquality e
