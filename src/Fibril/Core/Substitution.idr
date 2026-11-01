-- Structural substitution laws checked by Idris 2, not a Fibril typing theorem.
-- Binding background: DEBRUIJN72; exact proof scope: docs/substitution.md.
module Fibril.Core.Substitution

import Data.Fin
import Fibril.Core.Term
import Fibril.Core.Renaming

%default total

liftAgreement : (left, right : Fin n -> Term m) ->
                ((i : Fin n) -> left i = right i) ->
                (i : Fin (S n)) -> liftSubstitution left i = liftSubstitution right i
liftAgreement left right agree FZ = Refl
liftAgreement left right agree (FS i) = cong weaken (agree i)

||| Pointwise equal replacements yield equal substituted syntax.
||| No function-extensionality axiom or term-typing assumption is needed.
public export
substituteCongruent : (left, right : Fin n -> Term m) ->
                      ((i : Fin n) -> left i = right i) ->
                      (term : Term n) ->
                      substituteTerm left term = substituteTerm right term
substituteCongruent left right agree (Variable i) = agree i
substituteCongruent left right agree (Universe _) = Refl
substituteCongruent left right agree UnitType = Refl
substituteCongruent left right agree UnitValue = Refl
substituteCongruent left right agree BoolType = Refl
substituteCongruent left right agree BoolTrue = Refl
substituteCongruent left right agree BoolFalse = Refl
substituteCongruent left right agree StringType = Refl
substituteCongruent left right agree (StringValue _) = Refl
substituteCongruent left right agree (IOType value) = cong IOType (substituteCongruent left right agree value)
substituteCongruent left right agree (IOPure value) = cong IOPure (substituteCongruent left right agree value)
substituteCongruent left right agree (WriteLine value) = cong WriteLine (substituteCongruent left right agree value)
substituteCongruent left right agree (IOBind a b action next) =
  rewrite substituteCongruent left right agree a in
  rewrite substituteCongruent left right agree b in
  rewrite substituteCongruent left right agree action in
  rewrite substituteCongruent left right agree next in Refl
substituteCongruent left right agree (BoolCase condition yes no) =
  rewrite substituteCongruent left right agree condition in
  rewrite substituteCongruent left right agree yes in
  rewrite substituteCongruent left right agree no in Refl
substituteCongruent left right agree (Pi q domain body) =
  rewrite substituteCongruent left right agree domain in
  rewrite substituteCongruent (liftSubstitution left) (liftSubstitution right)
                            (liftAgreement left right agree) body in Refl
substituteCongruent left right agree (Lambda q domain body) =
  rewrite substituteCongruent left right agree domain in
  rewrite substituteCongruent (liftSubstitution left) (liftSubstitution right)
                            (liftAgreement left right agree) body in Refl
substituteCongruent left right agree (Apply function argument) =
  rewrite substituteCongruent left right agree function in
  rewrite substituteCongruent left right agree argument in Refl
substituteCongruent left right agree (StringAppend function argument) =
  rewrite substituteCongruent left right agree function in
  rewrite substituteCongruent left right agree argument in Refl
substituteCongruent left right agree (UnitCase scrutinee body) =
  rewrite substituteCongruent left right agree scrutinee in
  rewrite substituteCongruent left right agree body in Refl

liftVariables : (env : Fin n -> Fin m) -> (i : Fin (S n)) ->
                Variable (liftRenaming env i) = liftSubstitution (Variable . env) i
liftVariables env FZ = Refl
liftVariables env (FS i) = Refl

||| Renaming is exactly substitution by the renamed variables, including binders.
||| This relates syntax operations only; it does not authorize resource substitution.
public export
renameAsSubstitution : (env : Fin n -> Fin m) -> (term : Term n) ->
                       rename env term = substituteTerm (Variable . env) term
renameAsSubstitution env (Variable _) = Refl
renameAsSubstitution env (Universe _) = Refl
renameAsSubstitution env UnitType = Refl
renameAsSubstitution env UnitValue = Refl
renameAsSubstitution env BoolType = Refl
renameAsSubstitution env BoolTrue = Refl
renameAsSubstitution env BoolFalse = Refl
renameAsSubstitution env StringType = Refl
renameAsSubstitution env (StringValue _) = Refl
renameAsSubstitution env (IOType value) = cong IOType (renameAsSubstitution env value)
renameAsSubstitution env (IOPure value) = cong IOPure (renameAsSubstitution env value)
renameAsSubstitution env (WriteLine value) = cong WriteLine (renameAsSubstitution env value)
renameAsSubstitution env (IOBind a b action next) =
  rewrite renameAsSubstitution env a in
  rewrite renameAsSubstitution env b in
  rewrite renameAsSubstitution env action in
  rewrite renameAsSubstitution env next in Refl
renameAsSubstitution env (BoolCase condition yes no) =
  rewrite renameAsSubstitution env condition in
  rewrite renameAsSubstitution env yes in
  rewrite renameAsSubstitution env no in Refl
renameAsSubstitution env (Pi q domain body) =
  rewrite renameAsSubstitution env domain in
  rewrite renameAsSubstitution (liftRenaming env) body in
  rewrite substituteCongruent (Variable . liftRenaming env)
                            (liftSubstitution (Variable . env))
                            (liftVariables env) body in Refl
renameAsSubstitution env (Lambda q domain body) =
  rewrite renameAsSubstitution env domain in
  rewrite renameAsSubstitution (liftRenaming env) body in
  rewrite substituteCongruent (Variable . liftRenaming env)
                            (liftSubstitution (Variable . env))
                            (liftVariables env) body in Refl
renameAsSubstitution env (Apply function argument) =
  rewrite renameAsSubstitution env function in
  rewrite renameAsSubstitution env argument in Refl
renameAsSubstitution env (StringAppend function argument) =
  rewrite renameAsSubstitution env function in
  rewrite renameAsSubstitution env argument in Refl
renameAsSubstitution env (UnitCase scrutinee body) =
  rewrite renameAsSubstitution env scrutinee in
  rewrite renameAsSubstitution env body in Refl

||| Identity substitution follows from variable correspondence and renaming identity.
public export
substituteIdentity : (term : Term n) -> substituteTerm Variable term = term
substituteIdentity term =
  trans (sym (renameAsSubstitution Prelude.id term)) (renameIdentity term)
