-- Root beta-step compatibility of the actual reducer, not subject reduction.
module Fibril.Core.Reduction.Beta

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Reduction
import Fibril.Core.Substitution.Instantiation

%default total

||| A known root beta redex still contracts to the renamed contractum.
||| This is about Reduction.step itself, without typing or resource premises.
public export
renameBetaStep : (env : Fin n -> Fin m) -> (q : Quantity) ->
                 (domain : Term n) -> (body : Term (S n)) -> (argument : Term n) ->
                 step (rename env (Apply (Lambda q domain body) argument)) =
                   Just (rename env (instantiateTerm argument body))
renameBetaStep env q domain body argument =
  cong Just (sym (renameInstantiation env argument body))

||| Substitution preserves a known root beta contraction.
||| Not a statement that arbitrary substitution preserves the full step strategy:
||| substitution can introduce an earlier redex into otherwise neutral syntax.
public export
substituteBetaStep : (sigma : Fin n -> Term m) -> (q : Quantity) ->
                     (domain : Term n) -> (body : Term (S n)) -> (argument : Term n) ->
                     step (substituteTerm sigma (Apply (Lambda q domain body) argument)) =
                       Just (substituteTerm sigma (instantiateTerm argument body))
substituteBetaStep sigma q domain body argument =
  cong Just (sym (substituteInstantiation sigma argument body))
