module CommonApplicationWrongFace

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

-- The ambient face requires False, but this valuation assigns True.
bad : {ps : carrier (commonDependentPathEnvironmentSetoid [] [LBool])} ->
  {adm : DependentPathAdmissible CommonApplicationFixture.declarations ps} ->
  (w : HigherOrderCommonShadowPath CommonApplicationFixture.abstraction ps adm) ->
  related (commonTypeSetoid LBool)
    (applyMorphism (dependentPathSemantics (pathWitness (higherOrderCommonPathApplication w Zero)) (\_ => (True, True))) ((), ps))
    (applyMorphism (higherOrderCommonPathEndpoint w False (\_ => (True, True))) ((), ps))
bad w = higherOrderCommonPathApplicationBoundary w False () (\_ => (True, True)) Refl
