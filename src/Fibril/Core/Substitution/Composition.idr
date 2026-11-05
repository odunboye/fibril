-- Structural substitution fusion/composition proofs, checked by Idris 2.
-- No typed/quantitative substitution or reduction-preservation claim.
module Fibril.Core.Substitution.Composition

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Renaming
import Fibril.Core.Substitution

%default total

mutual
  liftRenameSubstitution : (env : Fin m -> Fin k) -> (sigma : Fin n -> Term m) ->
                           (i : Fin (S n)) ->
                           rename (liftRenaming env) (liftSubstitution sigma i) =
                             liftSubstitution (rename env . sigma) i
  liftRenameSubstitution env sigma FZ = Refl
  liftRenameSubstitution env sigma (FS i) = renameWeakening env (sigma i)

  ||| Renaming every replacement agrees with renaming after substitution.
  public export
  renameAfterSubstitution : (env : Fin m -> Fin k) -> (sigma : Fin n -> Term m) ->
                            (term : Term n) ->
                            rename env (substituteTerm sigma term) =
                              substituteTerm (rename env . sigma) term
  renameAfterSubstitution env sigma (Variable _) = Refl
  renameAfterSubstitution env sigma (Universe _) = Refl
  renameAfterSubstitution env sigma UnitType = Refl
  renameAfterSubstitution env sigma UnitValue = Refl
  renameAfterSubstitution env sigma BoolType = Refl
  renameAfterSubstitution env sigma BoolTrue = Refl
  renameAfterSubstitution env sigma BoolFalse = Refl
  renameAfterSubstitution env sigma ReadLine = Refl
  renameAfterSubstitution env sigma (FileHandleValue _) = Refl
  renameAfterSubstitution env sigma StringType = Refl
  renameAfterSubstitution env sigma (StringValue _) = Refl
  renameAfterSubstitution env sigma (WithInputFile result path body) = rewrite renameAfterSubstitution env sigma result in rewrite renameAfterSubstitution env sigma path in rewrite renameAfterSubstitution env sigma body in Refl
  renameAfterSubstitution env sigma (IOType value) = cong IOType (renameAfterSubstitution env sigma value)
  renameAfterSubstitution env sigma (FileHandleType region) = cong FileHandleType (renameAfterSubstitution env sigma region)
  renameAfterSubstitution env sigma (NominalType key indices shape) = rewrite renameAfterSubstitutionTerms env sigma indices in rewrite renameAfterSubstitution env sigma shape in Refl
  renameAfterSubstitution env sigma (NominalValue ty value) = rewrite renameAfterSubstitution env sigma ty in rewrite renameAfterSubstitution env sigma value in Refl
  renameAfterSubstitution env sigma (NominalCase motive value branch) = rewrite renameAfterSubstitution env sigma motive in rewrite renameAfterSubstitution env sigma value in rewrite renameAfterSubstitution env sigma branch in Refl
  renameAfterSubstitution env sigma (VariantType arms) = rewrite renameAfterSubstitutionArms env sigma arms in Refl
  renameAfterSubstitution env sigma (VariantValue ty tag Nothing) = rewrite renameAfterSubstitution env sigma ty in Refl
  renameAfterSubstitution env sigma (VariantValue ty tag (Just value)) = rewrite renameAfterSubstitution env sigma ty in rewrite renameAfterSubstitution env sigma value in Refl
  renameAfterSubstitution env sigma (VariantCase motive value branches) = rewrite renameAfterSubstitution env sigma motive in rewrite renameAfterSubstitution env sigma value in rewrite renameAfterSubstitutionTerms env sigma branches in Refl
  renameAfterSubstitution env sigma (BoxType q value) = cong (BoxType q) (renameAfterSubstitution env sigma value)
  renameAfterSubstitution env sigma (IOPure value) = cong IOPure (renameAfterSubstitution env sigma value)
  renameAfterSubstitution env sigma (WriteLine value) = cong WriteLine (renameAfterSubstitution env sigma value)
  renameAfterSubstitution env sigma (IOBind a b action next) =
    rewrite renameAfterSubstitution env sigma a in
    rewrite renameAfterSubstitution env sigma b in
    rewrite renameAfterSubstitution env sigma action in
    rewrite renameAfterSubstitution env sigma next in Refl
  renameAfterSubstitution env sigma (BoolCase condition yes no) =
    rewrite renameAfterSubstitution env sigma condition in
    rewrite renameAfterSubstitution env sigma yes in
    rewrite renameAfterSubstitution env sigma no in Refl
  renameAfterSubstitution env sigma (PairCase motive scrutinee branch) =
    rewrite renameAfterSubstitution env sigma motive in
    rewrite renameAfterSubstitution env sigma scrutinee in
    rewrite renameAfterSubstitution env sigma branch in Refl
  renameAfterSubstitution env sigma (BoxCase motive scrutinee branch) =
    rewrite renameAfterSubstitution env sigma motive in
    rewrite renameAfterSubstitution env sigma scrutinee in
    rewrite renameAfterSubstitution env sigma branch in Refl
  renameAfterSubstitution env sigma (PairValue annotation firstValue secondValue) =
    rewrite renameAfterSubstitution env sigma annotation in
    rewrite renameAfterSubstitution env sigma firstValue in
    rewrite renameAfterSubstitution env sigma secondValue in Refl
  renameAfterSubstitution env sigma (Pi q domain body) =
    rewrite renameAfterSubstitution env sigma domain in
    rewrite renameAfterSubstitution (liftRenaming env) (liftSubstitution sigma) body in
    rewrite substituteCongruent (rename (liftRenaming env) . liftSubstitution sigma)
                              (liftSubstitution (rename env . sigma))
                              (liftRenameSubstitution env sigma) body in Refl
  renameAfterSubstitution env sigma (Sigma q r domain body) =
    rewrite renameAfterSubstitution env sigma domain in
    rewrite renameAfterSubstitution (liftRenaming env) (liftSubstitution sigma) body in
    rewrite substituteCongruent (rename (liftRenaming env) . liftSubstitution sigma)
                              (liftSubstitution (rename env . sigma))
                              (liftRenameSubstitution env sigma) body in Refl
  renameAfterSubstitution env sigma (Lambda q domain body) =
    rewrite renameAfterSubstitution env sigma domain in
    rewrite renameAfterSubstitution (liftRenaming env) (liftSubstitution sigma) body in
    rewrite substituteCongruent (rename (liftRenaming env) . liftSubstitution sigma)
                              (liftSubstitution (rename env . sigma))
                              (liftRenameSubstitution env sigma) body in Refl
  renameAfterSubstitution env sigma (Apply function argument) =
    rewrite renameAfterSubstitution env sigma function in
    rewrite renameAfterSubstitution env sigma argument in Refl
  renameAfterSubstitution env sigma (StringAppend function argument) =
    rewrite renameAfterSubstitution env sigma function in
    rewrite renameAfterSubstitution env sigma argument in Refl
  renameAfterSubstitution env sigma (BoxValue function argument) =
    rewrite renameAfterSubstitution env sigma function in
    rewrite renameAfterSubstitution env sigma argument in Refl
  renameAfterSubstitution env sigma (StringEqual function argument) =
    rewrite renameAfterSubstitution env sigma function in
    rewrite renameAfterSubstitution env sigma argument in Refl
  renameAfterSubstitution env sigma (UnitCase scrutinee body) =
    rewrite renameAfterSubstitution env sigma scrutinee in
    rewrite renameAfterSubstitution env sigma body in Refl

  liftSubstituteRenaming : (env : Fin n -> Fin m) -> (sigma : Fin m -> Term k) ->
                          (i : Fin (S n)) ->
                          liftSubstitution sigma (liftRenaming env i) =
                            liftSubstitution (sigma . env) i
  liftSubstituteRenaming env sigma FZ = Refl
  liftSubstituteRenaming env sigma (FS i) = Refl

  ||| Substitution after renaming agrees with composing the index map first.
  public export
  substituteAfterRenaming : (env : Fin n -> Fin m) -> (sigma : Fin m -> Term k) ->
                            (term : Term n) ->
                            substituteTerm sigma (rename env term) =
                              substituteTerm (sigma . env) term
  substituteAfterRenaming env sigma (Variable _) = Refl
  substituteAfterRenaming env sigma (Universe _) = Refl
  substituteAfterRenaming env sigma UnitType = Refl
  substituteAfterRenaming env sigma UnitValue = Refl
  substituteAfterRenaming env sigma BoolType = Refl
  substituteAfterRenaming env sigma BoolTrue = Refl
  substituteAfterRenaming env sigma BoolFalse = Refl
  substituteAfterRenaming env sigma ReadLine = Refl
  substituteAfterRenaming env sigma (FileHandleValue _) = Refl
  substituteAfterRenaming env sigma StringType = Refl
  substituteAfterRenaming env sigma (StringValue _) = Refl
  substituteAfterRenaming env sigma (WithInputFile result path body) = rewrite substituteAfterRenaming env sigma result in rewrite substituteAfterRenaming env sigma path in rewrite substituteAfterRenaming env sigma body in Refl
  substituteAfterRenaming env sigma (IOType value) = cong IOType (substituteAfterRenaming env sigma value)
  substituteAfterRenaming env sigma (FileHandleType region) = cong FileHandleType (substituteAfterRenaming env sigma region)
  substituteAfterRenaming env sigma (NominalType key indices shape) = rewrite substituteAfterRenamingTerms env sigma indices in rewrite substituteAfterRenaming env sigma shape in Refl
  substituteAfterRenaming env sigma (NominalValue ty value) = rewrite substituteAfterRenaming env sigma ty in rewrite substituteAfterRenaming env sigma value in Refl
  substituteAfterRenaming env sigma (NominalCase motive value branch) = rewrite substituteAfterRenaming env sigma motive in rewrite substituteAfterRenaming env sigma value in rewrite substituteAfterRenaming env sigma branch in Refl
  substituteAfterRenaming env sigma (VariantType arms) = rewrite substituteAfterRenamingArms env sigma arms in Refl
  substituteAfterRenaming env sigma (VariantValue ty tag Nothing) = rewrite substituteAfterRenaming env sigma ty in Refl
  substituteAfterRenaming env sigma (VariantValue ty tag (Just value)) = rewrite substituteAfterRenaming env sigma ty in rewrite substituteAfterRenaming env sigma value in Refl
  substituteAfterRenaming env sigma (VariantCase motive value branches) = rewrite substituteAfterRenaming env sigma motive in rewrite substituteAfterRenaming env sigma value in rewrite substituteAfterRenamingTerms env sigma branches in Refl
  substituteAfterRenaming env sigma (BoxType q value) = cong (BoxType q) (substituteAfterRenaming env sigma value)
  substituteAfterRenaming env sigma (IOPure value) = cong IOPure (substituteAfterRenaming env sigma value)
  substituteAfterRenaming env sigma (WriteLine value) = cong WriteLine (substituteAfterRenaming env sigma value)
  substituteAfterRenaming env sigma (IOBind a b action next) =
    rewrite substituteAfterRenaming env sigma a in
    rewrite substituteAfterRenaming env sigma b in
    rewrite substituteAfterRenaming env sigma action in
    rewrite substituteAfterRenaming env sigma next in Refl
  substituteAfterRenaming env sigma (BoolCase condition yes no) =
    rewrite substituteAfterRenaming env sigma condition in
    rewrite substituteAfterRenaming env sigma yes in
    rewrite substituteAfterRenaming env sigma no in Refl
  substituteAfterRenaming env sigma (PairCase motive scrutinee branch) =
    rewrite substituteAfterRenaming env sigma motive in
    rewrite substituteAfterRenaming env sigma scrutinee in
    rewrite substituteAfterRenaming env sigma branch in Refl
  substituteAfterRenaming env sigma (BoxCase motive scrutinee branch) =
    rewrite substituteAfterRenaming env sigma motive in
    rewrite substituteAfterRenaming env sigma scrutinee in
    rewrite substituteAfterRenaming env sigma branch in Refl
  substituteAfterRenaming env sigma (PairValue annotation firstValue secondValue) =
    rewrite substituteAfterRenaming env sigma annotation in
    rewrite substituteAfterRenaming env sigma firstValue in
    rewrite substituteAfterRenaming env sigma secondValue in Refl
  substituteAfterRenaming env sigma (Pi q domain body) =
    rewrite substituteAfterRenaming env sigma domain in
    rewrite substituteAfterRenaming (liftRenaming env) (liftSubstitution sigma) body in
    rewrite substituteCongruent (liftSubstitution sigma . liftRenaming env)
                              (liftSubstitution (sigma . env))
                              (liftSubstituteRenaming env sigma) body in Refl
  substituteAfterRenaming env sigma (Sigma q r domain body) =
    rewrite substituteAfterRenaming env sigma domain in
    rewrite substituteAfterRenaming (liftRenaming env) (liftSubstitution sigma) body in
    rewrite substituteCongruent (liftSubstitution sigma . liftRenaming env)
                              (liftSubstitution (sigma . env))
                              (liftSubstituteRenaming env sigma) body in Refl
  substituteAfterRenaming env sigma (Lambda q domain body) =
    rewrite substituteAfterRenaming env sigma domain in
    rewrite substituteAfterRenaming (liftRenaming env) (liftSubstitution sigma) body in
    rewrite substituteCongruent (liftSubstitution sigma . liftRenaming env)
                              (liftSubstitution (sigma . env))
                              (liftSubstituteRenaming env sigma) body in Refl
  substituteAfterRenaming env sigma (Apply function argument) =
    rewrite substituteAfterRenaming env sigma function in
    rewrite substituteAfterRenaming env sigma argument in Refl
  substituteAfterRenaming env sigma (StringAppend function argument) =
    rewrite substituteAfterRenaming env sigma function in
    rewrite substituteAfterRenaming env sigma argument in Refl
  substituteAfterRenaming env sigma (BoxValue function argument) =
    rewrite substituteAfterRenaming env sigma function in
    rewrite substituteAfterRenaming env sigma argument in Refl
  substituteAfterRenaming env sigma (StringEqual function argument) =
    rewrite substituteAfterRenaming env sigma function in
    rewrite substituteAfterRenaming env sigma argument in Refl
  substituteAfterRenaming env sigma (UnitCase scrutinee body) =
    rewrite substituteAfterRenaming env sigma scrutinee in
    rewrite substituteAfterRenaming env sigma body in Refl

  ||| A lifted substitution commutes with adding a fresh variable to syntax.
  public export
  substituteWeakening : (sigma : Fin n -> Term m) -> (term : Term n) ->
                        substituteTerm (liftSubstitution sigma) (weaken term) =
                          weaken (substituteTerm sigma term)
  substituteWeakening sigma term =
    trans (substituteAfterRenaming FS (liftSubstitution sigma) term)
          (sym (renameAfterSubstitution FS sigma term))

  liftComposition : (first : Fin n -> Term m) -> (second : Fin m -> Term k) ->
                    (i : Fin (S n)) ->
                    substituteTerm (liftSubstitution second) (liftSubstitution first i) =
                      liftSubstitution (substituteTerm second . first) i
  liftComposition first second FZ = Refl
  liftComposition first second (FS i) = substituteWeakening second (first i)

  ||| Sequential simultaneous substitutions agree with substituting replacements.
  ||| All scopes/quantities and all raw scoped terms are covered, not typed derivations.
  public export
  substituteComposition : (first : Fin n -> Term m) -> (second : Fin m -> Term k) ->
                          (term : Term n) ->
                          substituteTerm second (substituteTerm first term) =
                            substituteTerm (substituteTerm second . first) term
  substituteComposition first second (Variable _) = Refl
  substituteComposition first second (Universe _) = Refl
  substituteComposition first second UnitType = Refl
  substituteComposition first second UnitValue = Refl
  substituteComposition first second BoolType = Refl
  substituteComposition first second BoolTrue = Refl
  substituteComposition first second BoolFalse = Refl
  substituteComposition first second ReadLine = Refl
  substituteComposition first second (FileHandleValue _) = Refl
  substituteComposition first second StringType = Refl
  substituteComposition first second (StringValue _) = Refl
  substituteComposition first second (WithInputFile result path body) = rewrite substituteComposition first second result in rewrite substituteComposition first second path in rewrite substituteComposition first second body in Refl
  substituteComposition first second (IOType value) = cong IOType (substituteComposition first second value)
  substituteComposition first second (FileHandleType region) = cong FileHandleType (substituteComposition first second region)
  substituteComposition first second (NominalType key indices shape) = rewrite substituteCompositionTerms first second indices in rewrite substituteComposition first second shape in Refl
  substituteComposition first second (NominalValue ty value) = rewrite substituteComposition first second ty in rewrite substituteComposition first second value in Refl
  substituteComposition first second (NominalCase motive value branch) = rewrite substituteComposition first second motive in rewrite substituteComposition first second value in rewrite substituteComposition first second branch in Refl
  substituteComposition first second (VariantType arms) = rewrite substituteCompositionArms first second arms in Refl
  substituteComposition first second (VariantValue ty tag Nothing) = rewrite substituteComposition first second ty in Refl
  substituteComposition first second (VariantValue ty tag (Just value)) = rewrite substituteComposition first second ty in rewrite substituteComposition first second value in Refl
  substituteComposition first second (VariantCase motive value branches) = rewrite substituteComposition first second motive in rewrite substituteComposition first second value in rewrite substituteCompositionTerms first second branches in Refl
  substituteComposition first second (BoxType q value) = cong (BoxType q) (substituteComposition first second value)
  substituteComposition first second (IOPure value) = cong IOPure (substituteComposition first second value)
  substituteComposition first second (WriteLine value) = cong WriteLine (substituteComposition first second value)
  substituteComposition first second (IOBind a b action next) =
    rewrite substituteComposition first second a in
    rewrite substituteComposition first second b in
    rewrite substituteComposition first second action in
    rewrite substituteComposition first second next in Refl
  substituteComposition first second (BoolCase condition yes no) =
    rewrite substituteComposition first second condition in
    rewrite substituteComposition first second yes in
    rewrite substituteComposition first second no in Refl
  substituteComposition first second (PairCase motive scrutinee branch) =
    rewrite substituteComposition first second motive in
    rewrite substituteComposition first second scrutinee in
    rewrite substituteComposition first second branch in Refl
  substituteComposition first second (BoxCase motive scrutinee branch) =
    rewrite substituteComposition first second motive in
    rewrite substituteComposition first second scrutinee in
    rewrite substituteComposition first second branch in Refl
  substituteComposition first second (PairValue annotation firstValue secondValue) =
    rewrite substituteComposition first second annotation in
    rewrite substituteComposition first second firstValue in
    rewrite substituteComposition first second secondValue in Refl
  substituteComposition first second (Pi q domain body) =
    rewrite substituteComposition first second domain in
    rewrite substituteComposition (liftSubstitution first) (liftSubstitution second) body in
    rewrite substituteCongruent (substituteTerm (liftSubstitution second) . liftSubstitution first)
                              (liftSubstitution (substituteTerm second . first))
                              (liftComposition first second) body in Refl
  substituteComposition first second (Sigma q r domain body) =
    rewrite substituteComposition first second domain in
    rewrite substituteComposition (liftSubstitution first) (liftSubstitution second) body in
    rewrite substituteCongruent (substituteTerm (liftSubstitution second) . liftSubstitution first)
                              (liftSubstitution (substituteTerm second . first))
                              (liftComposition first second) body in Refl
  substituteComposition first second (Lambda q domain body) =
    rewrite substituteComposition first second domain in
    rewrite substituteComposition (liftSubstitution first) (liftSubstitution second) body in
    rewrite substituteCongruent (substituteTerm (liftSubstitution second) . liftSubstitution first)
                              (liftSubstitution (substituteTerm second . first))
                              (liftComposition first second) body in Refl
  substituteComposition first second (Apply function argument) =
    rewrite substituteComposition first second function in
    rewrite substituteComposition first second argument in Refl
  substituteComposition first second (StringAppend function argument) =
    rewrite substituteComposition first second function in
    rewrite substituteComposition first second argument in Refl
  substituteComposition first second (BoxValue function argument) =
    rewrite substituteComposition first second function in
    rewrite substituteComposition first second argument in Refl
  substituteComposition first second (StringEqual function argument) =
    rewrite substituteComposition first second function in
    rewrite substituteComposition first second argument in Refl
  substituteComposition first second (UnitCase scrutinee body) =
    rewrite substituteComposition first second scrutinee in
    rewrite substituteComposition first second body in Refl

  ||| Instantiation cannot affect a term weakened past the removed variable.
  public export
  instantiateWeakening : (value, term : Term n) ->
                         instantiateTerm value (weaken term) = term
  instantiateWeakening value term =
    trans (substituteAfterRenaming FS (replaceNewest value) term)
          (substituteIdentity term)


  renameAfterSubstitutionArms : (env : Fin m -> Fin k) -> (sigma : Fin n -> Term m) -> (xs : List (Maybe (Quantity, Term n))) -> renameArms env (substituteArms sigma xs) = substituteArms (rename env . sigma) xs
  renameAfterSubstitutionArms env sigma [] = Refl
  renameAfterSubstitutionArms env sigma (Nothing :: rest) = rewrite renameAfterSubstitutionArms env sigma rest in Refl
  renameAfterSubstitutionArms env sigma (Just (q, ty) :: rest) = rewrite renameAfterSubstitution env sigma ty in rewrite renameAfterSubstitutionArms env sigma rest in Refl

  renameAfterSubstitutionTerms : (env : Fin m -> Fin k) -> (sigma : Fin n -> Term m) -> (xs : List (Term n)) -> renameTerms env (substituteTerms sigma xs) = substituteTerms (rename env . sigma) xs
  renameAfterSubstitutionTerms env sigma [] = Refl
  renameAfterSubstitutionTerms env sigma (value :: rest) = rewrite renameAfterSubstitution env sigma value in rewrite renameAfterSubstitutionTerms env sigma rest in Refl

  substituteAfterRenamingArms : (env : Fin n -> Fin m) -> (sigma : Fin m -> Term k) -> (xs : List (Maybe (Quantity, Term n))) -> substituteArms sigma (renameArms env xs) = substituteArms (sigma . env) xs
  substituteAfterRenamingArms env sigma [] = Refl
  substituteAfterRenamingArms env sigma (Nothing :: rest) = rewrite substituteAfterRenamingArms env sigma rest in Refl
  substituteAfterRenamingArms env sigma (Just (q, ty) :: rest) = rewrite substituteAfterRenaming env sigma ty in rewrite substituteAfterRenamingArms env sigma rest in Refl

  substituteAfterRenamingTerms : (env : Fin n -> Fin m) -> (sigma : Fin m -> Term k) -> (xs : List (Term n)) -> substituteTerms sigma (renameTerms env xs) = substituteTerms (sigma . env) xs
  substituteAfterRenamingTerms env sigma [] = Refl
  substituteAfterRenamingTerms env sigma (value :: rest) = rewrite substituteAfterRenaming env sigma value in rewrite substituteAfterRenamingTerms env sigma rest in Refl

  substituteCompositionArms : (first : Fin n -> Term m) -> (second : Fin m -> Term k) -> (xs : List (Maybe (Quantity, Term n))) -> substituteArms second (substituteArms first xs) = substituteArms (\i => substituteTerm second (first i)) xs
  substituteCompositionArms first second [] = Refl
  substituteCompositionArms first second (Nothing :: rest) = rewrite substituteCompositionArms first second rest in Refl
  substituteCompositionArms first second (Just (q, ty) :: rest) = rewrite substituteComposition first second ty in rewrite substituteCompositionArms first second rest in Refl

  substituteCompositionTerms : (first : Fin n -> Term m) -> (second : Fin m -> Term k) -> (xs : List (Term n)) -> substituteTerms second (substituteTerms first xs) = substituteTerms (\i => substituteTerm second (first i)) xs
  substituteCompositionTerms first second [] = Refl
  substituteCompositionTerms first second (value :: rest) = rewrite substituteComposition first second value in rewrite substituteCompositionTerms first second rest in Refl
