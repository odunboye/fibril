module ShadowDeclaredCapture
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath

bad : PathDeclarations [] [LBool]
bad = DeclarePath (LRef LHere) (LBoolean False) NoPaths
