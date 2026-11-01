-- Instantiation naturality over raw syntax, checked by Idris 2.
-- These laws do not establish typed or quantitative substitution.
module Fibril.Core.Substitution.Instantiation

import Data.Fin
import Fibril.Core.Term
import Fibril.Core.Substitution
import Fibril.Core.Substitution.Composition

%default total

renameReplacement : (env : Fin n -> Fin m) -> (value : Term n) ->
                    (i : Fin (S n)) ->
                    rename env (replaceNewest value i) =
                      replaceNewest (rename env value) (liftRenaming env i)
renameReplacement env value FZ = Refl
renameReplacement env value (FS i) = Refl

||| Rename after instantiating, or rename the value and lifted body first.
public export
renameInstantiation : (env : Fin n -> Fin m) -> (value : Term n) ->
                      (body : Term (S n)) ->
                      rename env (instantiateTerm value body) =
                        instantiateTerm (rename env value) (rename (liftRenaming env) body)
renameInstantiation env value body =
  trans (renameAfterSubstitution env (replaceNewest value) body)
    (trans (substituteCongruent (rename env . replaceNewest value)
                              (replaceNewest (rename env value) . liftRenaming env)
                              (renameReplacement env value) body)
           (sym (substituteAfterRenaming (liftRenaming env)
                                       (replaceNewest (rename env value)) body)))

substituteReplacement : (sigma : Fin n -> Term m) -> (value : Term n) ->
                        (i : Fin (S n)) ->
                        substituteTerm sigma (replaceNewest value i) =
                          instantiateTerm (substituteTerm sigma value)
                                          (liftSubstitution sigma i)
substituteReplacement sigma value FZ = Refl
substituteReplacement sigma value (FS i) =
  sym (instantiateWeakening (substituteTerm sigma value) (sigma i))

||| Substitute after instantiating, or substitute the value and lifted body first.
||| The older-variable case crucially uses weakening/instantiation cancellation.
public export
substituteInstantiation : (sigma : Fin n -> Term m) -> (value : Term n) ->
                          (body : Term (S n)) ->
                          substituteTerm sigma (instantiateTerm value body) =
                            instantiateTerm (substituteTerm sigma value)
                                            (substituteTerm (liftSubstitution sigma) body)
substituteInstantiation sigma value body =
  trans (substituteComposition (replaceNewest value) sigma body)
    (trans (substituteCongruent (substituteTerm sigma . replaceNewest value)
                              (instantiateTerm (substituteTerm sigma value) . liftSubstitution sigma)
                              (substituteReplacement sigma value) body)
           (sym (substituteComposition (liftSubstitution sigma)
                                       (replaceNewest (substituteTerm sigma value)) body)))
