module ShadowFaceEscape
import Data.Vect
import Data.Fin
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.OpenPath

import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Interval

decls : PathDeclarations [LBool] [LBool]
decls = DeclarePath (LRef LHere) (LBoolean False) NoPaths
bad : DeclaredEndpoint ShadowFaceEscape.decls (the (ScopedFace 1) STop) (NeutralAt LHere (Var FZ)) (Embed (LRef LHere))
bad = DeclaredLeft DeclaredHere Refl
