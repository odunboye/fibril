module CommonApplicationWrongPathWitness

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
import CommonApplicationFixture

%default total

-- The application API requires evidence for its exact source path index.
bad : {ps : carrier (commonDependentPathEnvironmentSetoid [] [LBool])} ->
  {adm : DependentPathAdmissible CommonApplicationFixture.declarations ps} ->
  (w : HigherOrderCommonShadowPath CommonApplicationFixture.abstraction ps adm) ->
  HigherOrderPathWitness [] [LBool] LBool 1 (applyCommonShadowPath CommonApplicationFixture.otherAbstraction Zero)
bad w = higherOrderCommonPathApplication {path = CommonApplicationFixture.otherAbstraction} w Zero
