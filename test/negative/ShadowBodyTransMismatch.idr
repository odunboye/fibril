module ShadowBodyTransMismatch
import Data.Vect
import Data.Fin
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Interval

decls : PathDeclarations [] [LBool, LBool]
decls = DeclarePath (LBoolean False) (LBoolean False)
          (DeclarePath (LBoolean True) (LBoolean True) NoPaths)

first : BodyEqual ShadowBodyTransMismatch.decls (the (ScopedFace 0) STop)
  (NeutralAt LHere Zero) (Embed (LBoolean False))
first = BodyEndpoint (DeclaredLeft DeclaredHere Refl)

second : BodyEqual ShadowBodyTransMismatch.decls (the (ScopedFace 0) STop)
  (Embed (LBoolean True)) (NeutralAt (LThere LHere) Zero)
second = BodySym (BodyEndpoint (DeclaredLeft (DeclaredThere DeclaredHere) Refl))

bad : BodyEqual ShadowBodyTransMismatch.decls (the (ScopedFace 0) STop)
  (NeutralAt LHere Zero) (NeutralAt (LThere LHere) Zero)
bad = BodyTrans ShadowBodyTransMismatch.first ShadowBodyTransMismatch.second
