-- Root beta-step compatibility of the actual reducer, not subject reduction.
module Fibril.Core.Reduction.Beta

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Reduction
import Fibril.Core.Substitution.Instantiation

%default total

||| Root selection commutes with scope transport at every valid or invalid tag.
public export
renameVariantContract : (env : Fin n -> Fin m) -> (tag : Nat) ->
  (payload : Maybe (Term n)) -> (branches : List (Term n)) ->
  map (rename env) (variantContract tag payload branches) =
    variantContract tag (map (rename env) payload) (renameTerms env branches)
renameVariantContract env _ payload [] = Refl
renameVariantContract env Z Nothing (branch :: rest) = Refl
renameVariantContract env Z (Just value) (branch :: rest) = Refl
renameVariantContract env (S tag) payload (branch :: rest) = renameVariantContract env tag payload rest

public export
substituteVariantContract : (env : Fin n -> Term m) -> (tag : Nat) ->
  (payload : Maybe (Term n)) -> (branches : List (Term n)) ->
  map (substituteTerm env) (variantContract tag payload branches) =
    variantContract tag (map (substituteTerm env) payload) (substituteTerms env branches)
substituteVariantContract env _ payload [] = Refl
substituteVariantContract env Z Nothing (branch :: rest) = Refl
substituteVariantContract env Z (Just value) (branch :: rest) = Refl
substituteVariantContract env (S tag) payload (branch :: rest) = substituteVariantContract env tag payload rest

||| Actual reducer equations at a known selected nullary/payload root.
public export
renameVariantNullaryStep : (env : Fin n -> Fin m) -> (p, ty, branch : Term n) -> (rest : List (Term n)) ->
  step (rename env (VariantCase p (VariantValue ty 0 Nothing) (branch :: rest))) = Just (rename env branch)
renameVariantNullaryStep env p ty branch rest = Refl

public export
substituteVariantNullaryStep : (env : Fin n -> Term m) -> (p, ty, branch : Term n) -> (rest : List (Term n)) ->
  step (substituteTerm env (VariantCase p (VariantValue ty 0 Nothing) (branch :: rest))) = Just (substituteTerm env branch)
substituteVariantNullaryStep env p ty branch rest = Refl

public export
renameVariantPayloadStep : (env : Fin n -> Fin m) -> (p, ty, value, branch : Term n) -> (rest : List (Term n)) ->
  step (rename env (VariantCase p (VariantValue ty 0 (Just value)) (branch :: rest))) = Just (rename env (Apply branch value))
renameVariantPayloadStep env p ty value branch rest = Refl

public export
substituteVariantPayloadStep : (env : Fin n -> Term m) -> (p, ty, value, branch : Term n) -> (rest : List (Term n)) ->
  step (substituteTerm env (VariantCase p (VariantValue ty 0 (Just value)) (branch :: rest))) = Just (substituteTerm env (Apply branch value))
substituteVariantPayloadStep env p ty value branch rest = Refl

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
