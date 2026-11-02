-- Root beta-step compatibility of the actual reducer, not subject reduction.
module Fibril.Core.Reduction.Beta

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Reduction
import Fibril.Core.Substitution.Instantiation

%default total

||| A known unary elimination contracts into one ordinary application.
public export
renameBoxCaseStep : (env : Fin n -> Fin m) -> (motive, ty, value, branch : Term n) ->
  step (rename env (BoxCase motive (BoxValue ty value) branch)) =
    Just (rename env (Apply branch value))
renameBoxCaseStep env motive ty value branch = Refl

public export
substituteBoxCaseStep : (env : Fin n -> Term m) -> (motive, ty, value, branch : Term n) ->
  step (substituteTerm env (BoxCase motive (BoxValue ty value) branch)) =
    Just (substituteTerm env (Apply branch value))
substituteBoxCaseStep env motive ty value branch = Refl

||| Pair elimination opens into ordinary applications. Subsequent substitution
||| uses the existing capture-safe lambda machinery, not an ad hoc two-index map.
public export
renamePairCaseStep : (env : Fin n -> Fin m) -> (motive, ty, first, second, branch : Term n) ->
  step (rename env (PairCase motive (PairValue ty first second) branch)) =
    Just (rename env (Apply (Apply branch first) second))
renamePairCaseStep env motive ty first second branch = Refl

public export
substitutePairCaseStep : (env : Fin n -> Term m) -> (motive, ty, first, second, branch : Term n) ->
  step (substituteTerm env (PairCase motive (PairValue ty first second) branch)) =
    Just (substituteTerm env (Apply (Apply branch first) second))
substitutePairCaseStep env motive ty first second branch = Refl

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
