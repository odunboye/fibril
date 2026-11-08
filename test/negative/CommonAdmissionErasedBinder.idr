module CommonAdmissionErasedBinder

import Data.Vect
import Fibril.Core.Usage
import Fibril.Core.Quantity
import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Quantitative.Usage

-- The corresponding ALam (AVar FZ) is admissible as a logical function,
-- but its erasure cannot grant permission to use an erased source binder.
bad : Uses (the (Term [] (Arrow Erased BoolTy BoolTy)) (Lam Erased (Ref Here))) []
bad = UseLam (UseRef Here) Refl
