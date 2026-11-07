module CommonFaceUsesReflection
import Data.Vect
import Fibril.Core.Quantity
import Fibril.Core.Usage

import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Quantitative.Usage
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Foundation.DeMorgan.Scope

bad : Uses (the (Term [BoolTy] BoolTy) (Ref Here)) [Erased]
bad = commonBodyEqual {decls = NoPaths} {face = the (ScopedFace 0) STop}
  (BodyRefl {x = Embed (shadowTerm (the (Term [BoolTy] BoolTy) (Ref Here)))})
