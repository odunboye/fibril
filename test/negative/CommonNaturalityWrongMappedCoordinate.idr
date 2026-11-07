module CommonNaturalityWrongMappedCoordinate

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
import CommonApplicationFixture

%default total

-- The new mapped-body API must substitute the application coordinate too.
bad : {ps : carrier (commonDependentPathEnvironmentSetoid [] [LBool])} ->
  {adm : DependentPathAdmissible CommonApplicationFixture.declarations ps} ->
  (w : HigherOrderCommonShadowPath CommonApplicationFixture.abstraction ps adm) ->
  HigherOrderPathWitness [] [LBool] LBool 1 (CPAt FZ (Var FZ))
bad w = higherOrderCommonPathMappedBodyApplication w (the (Fin 1 -> ScopedInterval 1) (\_ => Reverse (Var FZ))) (Var FZ)
