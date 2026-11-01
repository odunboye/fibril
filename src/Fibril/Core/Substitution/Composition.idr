-- Structural substitution fusion/composition proofs, checked by Idris 2.
-- No typed/quantitative substitution or reduction-preservation claim.
module Fibril.Core.Substitution.Composition

import Data.Fin
import Fibril.Core.Term
import Fibril.Core.Renaming
import Fibril.Core.Substitution

%default total

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
renameAfterSubstitution env sigma StringType = Refl
renameAfterSubstitution env sigma (StringValue _) = Refl
renameAfterSubstitution env sigma (BoolCase condition yes no) =
  rewrite renameAfterSubstitution env sigma condition in
  rewrite renameAfterSubstitution env sigma yes in
  rewrite renameAfterSubstitution env sigma no in Refl
renameAfterSubstitution env sigma (Pi q domain body) =
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
substituteAfterRenaming env sigma StringType = Refl
substituteAfterRenaming env sigma (StringValue _) = Refl
substituteAfterRenaming env sigma (BoolCase condition yes no) =
  rewrite substituteAfterRenaming env sigma condition in
  rewrite substituteAfterRenaming env sigma yes in
  rewrite substituteAfterRenaming env sigma no in Refl
substituteAfterRenaming env sigma (Pi q domain body) =
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
substituteComposition first second StringType = Refl
substituteComposition first second (StringValue _) = Refl
substituteComposition first second (BoolCase condition yes no) =
  rewrite substituteComposition first second condition in
  rewrite substituteComposition first second yes in
  rewrite substituteComposition first second no in Refl
substituteComposition first second (Pi q domain body) =
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
