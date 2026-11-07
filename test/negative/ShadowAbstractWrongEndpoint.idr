module ShadowAbstractWrongEndpoint
import Data.Vect
import Data.Fin
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Interval

decls : PathDeclarations [] [LBool]
decls = DeclarePath (LBoolean False) (LBoolean False) NoPaths
bad : DeclaredShadowPath ShadowAbstractWrongEndpoint.decls (the (ScopedFace 0) STop)
  (Embed (LBoolean True)) (Embed (LBoolean False))
bad = ShadowAbstract (NeutralAt LHere (Var FZ))
  (BodyEndpoint (DeclaredLeft DeclaredHere Refl)) (BodyEndpoint (DeclaredRight DeclaredHere Refl))
