module IndependentSubstitutionWrongIndex
import Data.Vect
import Data.Fin
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge

import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Foundation.DeMorgan.Face

import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

emptyImage : Fin 0 -> CommonTerm 0
emptyImage i impossible

emptyTyped : CommonSubstitutionTyped [] [] IndependentSubstitutionWrongIndex.emptyImage
emptyTyped v impossible

bad : CommonFaceEqual (the (CommonDeclarations [] [LBool, LBool]) (CommonDeclarePath (CBool True) (CBool False) CBoolType CBoolType
  (CommonDeclarePath (CBool False) (CBool True) CBoolType CBoolType CommonNoPaths)))
  (the (ScopedFace 1) (SEndpoint FZ False)) (CPAt (FS FZ) (Var FZ)) (CPOrdinary (CBool True)) LBool
bad = substituteCommonFaceEqual emptyImage emptyTyped
  (CommonDeclarePath (CBool True) (CBool False) CBoolType CBoolType
    (CommonDeclarePath (CBool False) (CBool True) CBoolType CBoolType CommonNoPaths))
  (CommonLeft CommonDeclaredHere Refl)
