module ShadowPathWrongEndpoint
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath

bad : ExactPath {context = []} {paths = []} {d = 0}
  (Embed (LBoolean True)) (Embed (LBoolean False))
bad = PathAbstract (Embed (LBoolean True)) Refl Refl
