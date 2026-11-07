module ShadowTypedBridgeWrongFace
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Foundation.DeMorgan.Face

import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

-- The source endpoint is independently valid at the left face.
source : DeclaredEndpoint (DeclarePath (LRef LHere) (LRef LHere) NoPaths)
  (the (ScopedFace 1) (SEndpoint FZ False))
  (NeutralAt LHere (Var FZ)) (Embed (LRef LHere))
source = DeclaredLeft DeclaredHere Refl

-- An opposite-face target check is not evidence for the left endpoint.
bad : TypedPath.boundedFaceEntails (the (ScopedFace 1) (SEndpoint FZ True))
  (scopedEndpoint (Var FZ) False) = True
bad = Refl
