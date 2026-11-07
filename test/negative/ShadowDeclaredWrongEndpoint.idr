module ShadowDeclaredWrongEndpoint
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.OpenPath

import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Interval

decls : PathDeclarations [LBool] [LBool]
decls = DeclarePath (LRef LHere) (LBoolean False) NoPaths
bad : DeclaredEndpoint ShadowDeclaredWrongEndpoint.decls STop (NeutralAt LHere Zero) (Embed (LBoolean True))
bad = DeclaredLeft DeclaredHere Refl
