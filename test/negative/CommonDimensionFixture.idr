module CommonDimensionFixture
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

public export
declarations : CommonDeclarations [] [LBool]
declarations = CommonDeclarePath (CBool True) (CBool False) CBoolType CBoolType CommonNoPaths

public export
source : CommonFaceEqual CommonDimensionFixture.declarations (the (ScopedFace 1) (SEndpoint FZ False))
  (CPAt FZ (Var FZ)) (CPOrdinary (CBool True)) LBool
source = CommonLeft CommonDeclaredHere Refl

public export
first : Fin 1 -> ScopedInterval 2
first FZ = Var FZ

public export
second : Fin 1 -> ScopedInterval 2
second FZ = Var (FS FZ)

public export
firstEvidence : CommonDimensionEvidence CommonDimensionFixture.first
  (the (ScopedFace 2) (SEndpoint FZ False)) CommonDimensionFixture.source
firstEvidence = CommonDimLeft CommonDeclaredHere Refl
