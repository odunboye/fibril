module CommonAbstractWrongIndex
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Face
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Cubical.Logical.PathContext


import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

source : DeclaredShadowPath NoPaths
  (the (ScopedFace 2) (SEndpoint FZ False)) (Embed (LBoolean True)) (Embed (LBoolean True))
source = ShadowAbstract (Embed (LBoolean True)) BodyRefl BodyRefl

bad : CommonShadowPath (commonDeclarations NoPaths)
  (the (ScopedFace 2) (SEndpoint (FS FZ) False)) (CPOrdinary (CBool True)) (CPOrdinary (CBool True)) LBool
bad = commonDeclaredShadowPath source
