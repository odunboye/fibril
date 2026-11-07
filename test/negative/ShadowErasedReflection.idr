module ShadowErasedReflection
import Data.Vect
import Fibril.Core.Quantity
import Fibril.Core.Usage

import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Quantitative.Usage
import Fibril.Cubical.Logical.Shadow

-- No shadow-to-Uses reflection API exists: its logical result has the wrong
-- type to serve directly as an erased source-use derivation.
bad : Uses (the (Term [BoolTy] BoolTy) (Ref Here)) [Erased]
bad = shadowTerm (the (Term [BoolTy] BoolTy) (Ref Here))
