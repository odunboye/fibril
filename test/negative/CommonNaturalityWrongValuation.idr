module CommonNaturalityWrongValuation

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

-- Reversal at (False, False) composes to (True, True), not (False, False).
-- Naturality cannot silently keep the uncomposed source valuation.
bad : {ps : carrier (commonDependentPathEnvironmentSetoid [] [LBool])} ->
  {adm : DependentPathAdmissible CommonApplicationFixture.declarations ps} ->
  (w : HigherOrderCommonShadowPath CommonApplicationFixture.abstraction ps adm) ->
  related (commonTypeSetoid LBool)
    (applyMorphism (dependentPathSemantics (pathWitness (mapHigherOrderPathDimensions (the (Fin 1 -> ScopedInterval 1) (\_ => Reverse (Var FZ)))
      (pathWitness (higherOrderCommonPathApplication w (Var FZ))))) (\_ => (False, False))) ((), ps))
    (applyMorphism (dependentPathSemantics (pathWitness (higherOrderCommonPathApplication w (Var FZ)))
      (\_ => (False, False))) ((), ps))
bad {ps} w = higherOrderCommonPathApplicationNaturality w (the (Fin 1 -> ScopedInterval 1) (\_ => Reverse (Var FZ))) (Var FZ)
  (\_ => (False, False)) ((), ps) ((), ps)
  (relationRefl (commonProductSetoid (commonEnvironmentSetoid []) (commonDependentPathEnvironmentSetoid [] [LBool])) ((), ps))
