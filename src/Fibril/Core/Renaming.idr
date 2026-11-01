-- Structural laws for Term.rename, checked by Idris 2, not by Fibril.
-- These establish no typing, reduction, usage, or cubical soundness theorem.
module Fibril.Core.Renaming

import Data.Fin
import Fibril.Core.Term

%default total

liftAgreement : (left, right : Fin n -> Fin m) ->
                ((i : Fin n) -> left i = right i) ->
                (i : Fin (S n)) -> liftRenaming left i = liftRenaming right i
liftAgreement left right agree FZ = Refl
liftAgreement left right agree (FS i) = cong FS (agree i)

||| Pointwise agreement suffices; no function-extensionality axiom is required.
public export
renameCongruent : (left, right : Fin n -> Fin m) ->
                  ((i : Fin n) -> left i = right i) ->
                  (term : Term n) -> rename left term = rename right term
renameCongruent left right agree (Variable i) = cong Variable (agree i)
renameCongruent left right agree (Universe _) = Refl
renameCongruent left right agree UnitType = Refl
renameCongruent left right agree UnitValue = Refl
renameCongruent left right agree BoolType = Refl
renameCongruent left right agree BoolTrue = Refl
renameCongruent left right agree BoolFalse = Refl
renameCongruent left right agree StringType = Refl
renameCongruent left right agree (StringValue _) = Refl
renameCongruent left right agree (IOType value) = cong IOType (renameCongruent left right agree value)
renameCongruent left right agree (IOPure value) = cong IOPure (renameCongruent left right agree value)
renameCongruent left right agree (WriteLine value) = cong WriteLine (renameCongruent left right agree value)
renameCongruent left right agree (IOBind a b action next) =
  rewrite renameCongruent left right agree a in
  rewrite renameCongruent left right agree b in
  rewrite renameCongruent left right agree action in
  rewrite renameCongruent left right agree next in Refl
renameCongruent left right agree (BoolCase condition yes no) =
  rewrite renameCongruent left right agree condition in
  rewrite renameCongruent left right agree yes in
  rewrite renameCongruent left right agree no in Refl
renameCongruent left right agree (Pi q domain body) =
  rewrite renameCongruent left right agree domain in
  rewrite renameCongruent (liftRenaming left) (liftRenaming right)
                         (liftAgreement left right agree) body in Refl
renameCongruent left right agree (Lambda q domain body) =
  rewrite renameCongruent left right agree domain in
  rewrite renameCongruent (liftRenaming left) (liftRenaming right)
                         (liftAgreement left right agree) body in Refl
renameCongruent left right agree (Apply function argument) =
  rewrite renameCongruent left right agree function in
  rewrite renameCongruent left right agree argument in Refl
renameCongruent left right agree (StringAppend function argument) =
  rewrite renameCongruent left right agree function in
  rewrite renameCongruent left right agree argument in Refl
renameCongruent left right agree (UnitCase scrutinee body) =
  rewrite renameCongruent left right agree scrutinee in
  rewrite renameCongruent left right agree body in Refl

liftIdentity : (i : Fin (S n)) -> liftRenaming Prelude.id i = i
liftIdentity FZ = Refl
liftIdentity (FS i) = Refl

||| Identity renaming preserves every scoped term, including beneath binders.
public export
renameIdentity : (term : Term n) -> rename Prelude.id term = term
renameIdentity (Variable _) = Refl
renameIdentity (Universe _) = Refl
renameIdentity UnitType = Refl
renameIdentity UnitValue = Refl
renameIdentity BoolType = Refl
renameIdentity BoolTrue = Refl
renameIdentity BoolFalse = Refl
renameIdentity StringType = Refl
renameIdentity (StringValue _) = Refl
renameIdentity (IOType value) = cong IOType (renameIdentity value)
renameIdentity (IOPure value) = cong IOPure (renameIdentity value)
renameIdentity (WriteLine value) = cong WriteLine (renameIdentity value)
renameIdentity (IOBind a b action next) =
  rewrite renameIdentity a in
  rewrite renameIdentity b in
  rewrite renameIdentity action in
  rewrite renameIdentity next in Refl
renameIdentity (BoolCase condition yes no) =
  rewrite renameIdentity condition in
  rewrite renameIdentity yes in
  rewrite renameIdentity no in Refl
renameIdentity (Pi q domain body) =
  rewrite renameIdentity domain in
  rewrite renameCongruent (liftRenaming Prelude.id) Prelude.id liftIdentity body in
  rewrite renameIdentity body in Refl
renameIdentity (Lambda q domain body) =
  rewrite renameIdentity domain in
  rewrite renameCongruent (liftRenaming Prelude.id) Prelude.id liftIdentity body in
  rewrite renameIdentity body in Refl
renameIdentity (Apply function argument) =
  rewrite renameIdentity function in
  rewrite renameIdentity argument in Refl
renameIdentity (StringAppend function argument) =
  rewrite renameIdentity function in
  rewrite renameIdentity argument in Refl
renameIdentity (UnitCase scrutinee body) =
  rewrite renameIdentity scrutinee in
  rewrite renameIdentity body in Refl

liftComposition : (first : Fin n -> Fin m) -> (second : Fin m -> Fin k) ->
                  (i : Fin (S n)) ->
                  liftRenaming second (liftRenaming first i) =
                    liftRenaming (second . first) i
liftComposition first second FZ = Refl
liftComposition first second (FS i) = Refl

||| Sequential renamings agree with composition in execution order.
||| This includes arbitrary (not necessarily injective) renamings.
public export
renameComposition : (first : Fin n -> Fin m) -> (second : Fin m -> Fin k) ->
                    (term : Term n) ->
                    rename second (rename first term) = rename (second . first) term
renameComposition first second (Variable _) = Refl
renameComposition first second (Universe _) = Refl
renameComposition first second UnitType = Refl
renameComposition first second UnitValue = Refl
renameComposition first second BoolType = Refl
renameComposition first second BoolTrue = Refl
renameComposition first second BoolFalse = Refl
renameComposition first second StringType = Refl
renameComposition first second (StringValue _) = Refl
renameComposition first second (IOType value) = cong IOType (renameComposition first second value)
renameComposition first second (IOPure value) = cong IOPure (renameComposition first second value)
renameComposition first second (WriteLine value) = cong WriteLine (renameComposition first second value)
renameComposition first second (IOBind a b action next) =
  rewrite renameComposition first second a in
  rewrite renameComposition first second b in
  rewrite renameComposition first second action in
  rewrite renameComposition first second next in Refl
renameComposition first second (BoolCase condition yes no) =
  rewrite renameComposition first second condition in
  rewrite renameComposition first second yes in
  rewrite renameComposition first second no in Refl
renameComposition first second (Pi q domain body) =
  rewrite renameComposition first second domain in
  rewrite renameComposition (liftRenaming first) (liftRenaming second) body in
  rewrite renameCongruent (liftRenaming second . liftRenaming first)
                         (liftRenaming (second . first))
                         (liftComposition first second) body in Refl
renameComposition first second (Lambda q domain body) =
  rewrite renameComposition first second domain in
  rewrite renameComposition (liftRenaming first) (liftRenaming second) body in
  rewrite renameCongruent (liftRenaming second . liftRenaming first)
                         (liftRenaming (second . first))
                         (liftComposition first second) body in Refl
renameComposition first second (Apply function argument) =
  rewrite renameComposition first second function in
  rewrite renameComposition first second argument in Refl
renameComposition first second (StringAppend function argument) =
  rewrite renameComposition first second function in
  rewrite renameComposition first second argument in Refl
renameComposition first second (UnitCase scrutinee body) =
  rewrite renameComposition first second scrutinee in
  rewrite renameComposition first second body in Refl

||| Renaming under a fresh binder commutes with weakening.
||| A structural ingredient for future substitution laws, not a typing theorem.
public export
renameWeakening : (env : Fin n -> Fin m) -> (term : Term n) ->
                  rename (liftRenaming env) (weaken term) = weaken (rename env term)
renameWeakening env term =
  trans (renameComposition FS (liftRenaming env) term)
    (trans (renameCongruent (liftRenaming env . FS) (FS . env) (\i => Refl) term)
           (sym (renameComposition env FS term)))
