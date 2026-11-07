module ShadowBodyWrongPath
import Data.Vect
import Data.Fin
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.OpenPath

import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Interval

decls : PathDeclarations [] [LBool, LBool]
decls = DeclarePath (LBoolean True) (LBoolean False) (DeclarePath (LBoolean False) (LBoolean True) NoPaths)
bad : BodyEqual ShadowBodyWrongPath.decls (the (ScopedFace 0) STop)
  (NeutralAt (LThere LHere) Zero) (Embed (LBoolean True))
bad = BodyEndpoint (DeclaredLeft DeclaredHere Refl)
