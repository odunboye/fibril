module CommonApplicationFixture

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Face

%default total

public export
declarations : CommonDeclarations [] [LBool]
declarations = CommonDeclarePath (CBool False) (CBool True) CBoolType CBoolType CommonNoPaths

public export
abstraction : CommonShadowPath {ctx = []} {paths = [LBool]} CommonApplicationFixture.declarations
  (the (ScopedFace 1) (SEndpoint FZ False)) (CPOrdinary (CBool False)) (CPOrdinary (CBool True)) LBool
abstraction = CommonAbstract (CPOrdinaryType CBoolType) (CPOrdinaryType CBoolType)
  (CPAt FZ (Var FZ)) (CPAtType LHere)
  (CommonLeft CommonDeclaredHere Refl) (CommonRight CommonDeclaredHere Refl)

public export
otherAbstraction : CommonShadowPath {ctx = []} {paths = [LBool]} CommonApplicationFixture.declarations
  (the (ScopedFace 1) (SEndpoint FZ False)) (CPAt FZ (Var FZ)) (CPAt FZ (Var FZ)) LBool
otherAbstraction = CommonAbstract (CPAtType LHere) (CPAtType LHere)
  (CPAt FZ (Var (FS FZ))) (CPAtType LHere)
  (CommonRefl (CPAtType LHere)) (CommonRefl (CPAtType LHere))
