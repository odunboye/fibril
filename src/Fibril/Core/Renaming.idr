-- Structural laws for Term.rename, checked by Idris 2, not by Fibril.
-- These establish no typing, reduction, usage, or cubical soundness theorem.
module Fibril.Core.Renaming

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term

%default total

mutual
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
  renameCongruent left right agree NatType = Refl
  renameCongruent left right agree NatZero = Refl
  renameCongruent left right agree (NatSucc x) = cong NatSucc (renameCongruent left right agree x)
  renameCongruent left right agree (NatRec p z s x) = rewrite renameCongruent left right agree p in rewrite renameCongruent left right agree z in rewrite renameCongruent left right agree s in rewrite renameCongruent left right agree x in Refl
  renameCongruent left right agree (NatRecRuntime p z s x) = rewrite renameCongruent left right agree p in rewrite renameCongruent left right agree z in rewrite renameCongruent left right agree s in rewrite renameCongruent left right agree x in Refl
  renameCongruent left right agree (RecType key) = Refl
  renameCongruent left right agree (RecEnd ty) = cong RecEnd (renameCongruent left right agree ty)
  renameCongruent left right agree (RecMore ty x) = rewrite renameCongruent left right agree ty in rewrite renameCongruent left right agree x in Refl
  renameCongruent left right agree (RecFold p z s x) = rewrite renameCongruent left right agree p in rewrite renameCongruent left right agree z in rewrite renameCongruent left right agree s in rewrite renameCongruent left right agree x in Refl
  renameCongruent left right agree StringType = Refl
  renameCongruent left right agree (StringValue _) = Refl
  renameCongruent left right agree (IOType value) = cong IOType (renameCongruent left right agree value)
  renameCongruent left right agree (NominalType key indices shape) = rewrite renameCongruentTerms left right agree indices in rewrite renameCongruent left right agree shape in Refl
  renameCongruent left right agree (NominalValue ty value) = rewrite renameCongruent left right agree ty in rewrite renameCongruent left right agree value in Refl
  renameCongruent left right agree (NominalCase motive value branch) = rewrite renameCongruent left right agree motive in rewrite renameCongruent left right agree value in rewrite renameCongruent left right agree branch in Refl
  renameCongruent left right agree (VariantType arms) = rewrite renameCongruentArms left right agree arms in Refl
  renameCongruent left right agree (VariantValue ty tag Nothing) = rewrite renameCongruent left right agree ty in Refl
  renameCongruent left right agree (VariantValue ty tag (Just value)) = rewrite renameCongruent left right agree ty in rewrite renameCongruent left right agree value in Refl
  renameCongruent left right agree (VariantCase motive value branches) = rewrite renameCongruent left right agree motive in rewrite renameCongruent left right agree value in rewrite renameCongruentTerms left right agree branches in Refl
  renameCongruent left right agree (BoxType q value) = cong (BoxType q) (renameCongruent left right agree value)
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
  renameCongruent left right agree (PairCase motive scrutinee branch) =
    rewrite renameCongruent left right agree motive in
    rewrite renameCongruent left right agree scrutinee in
    rewrite renameCongruent left right agree branch in Refl
  renameCongruent left right agree (BoxCase motive scrutinee branch) =
    rewrite renameCongruent left right agree motive in
    rewrite renameCongruent left right agree scrutinee in
    rewrite renameCongruent left right agree branch in Refl
  renameCongruent left right agree (PairValue annotation firstValue secondValue) =
    rewrite renameCongruent left right agree annotation in
    rewrite renameCongruent left right agree firstValue in
    rewrite renameCongruent left right agree secondValue in Refl
  renameCongruent left right agree (Pi q domain body) =
    rewrite renameCongruent left right agree domain in
    rewrite renameCongruent (liftRenaming left) (liftRenaming right)
                           (liftAgreement left right agree) body in Refl
  renameCongruent left right agree (Sigma q r domain body) =
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
  renameCongruent left right agree (BoxValue function argument) =
    rewrite renameCongruent left right agree function in
    rewrite renameCongruent left right agree argument in Refl
  renameCongruent left right agree (StringEqual function argument) =
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
  renameIdentity NatType = Refl
  renameIdentity NatZero = Refl
  renameIdentity (NatSucc x) = cong NatSucc (renameIdentity x)
  renameIdentity (NatRec p z s x) = rewrite renameIdentity p in rewrite renameIdentity z in rewrite renameIdentity s in rewrite renameIdentity x in Refl
  renameIdentity (NatRecRuntime p z s x) = rewrite renameIdentity p in rewrite renameIdentity z in rewrite renameIdentity s in rewrite renameIdentity x in Refl
  renameIdentity (RecType key) = Refl
  renameIdentity (RecEnd ty) = cong RecEnd (renameIdentity ty)
  renameIdentity (RecMore ty x) = rewrite renameIdentity ty in rewrite renameIdentity x in Refl
  renameIdentity (RecFold p z s x) = rewrite renameIdentity p in rewrite renameIdentity z in rewrite renameIdentity s in rewrite renameIdentity x in Refl
  renameIdentity StringType = Refl
  renameIdentity (StringValue _) = Refl
  renameIdentity (IOType value) = cong IOType (renameIdentity value)
  renameIdentity (NominalType key indices shape) = rewrite renameIdentityTerms indices in rewrite renameIdentity shape in Refl
  renameIdentity (NominalValue ty value) = rewrite renameIdentity ty in rewrite renameIdentity value in Refl
  renameIdentity (NominalCase motive value branch) = rewrite renameIdentity motive in rewrite renameIdentity value in rewrite renameIdentity branch in Refl
  renameIdentity (VariantType arms) = rewrite renameIdentityArms arms in Refl
  renameIdentity (VariantValue ty tag Nothing) = rewrite renameIdentity ty in Refl
  renameIdentity (VariantValue ty tag (Just value)) = rewrite renameIdentity ty in rewrite renameIdentity value in Refl
  renameIdentity (VariantCase motive value branches) = rewrite renameIdentity motive in rewrite renameIdentity value in rewrite renameIdentityTerms branches in Refl
  renameIdentity (BoxType q value) = cong (BoxType q) (renameIdentity value)
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
  renameIdentity (PairCase motive scrutinee branch) =
    rewrite renameIdentity motive in
    rewrite renameIdentity scrutinee in
    rewrite renameIdentity branch in Refl
  renameIdentity (BoxCase motive scrutinee branch) =
    rewrite renameIdentity motive in
    rewrite renameIdentity scrutinee in
    rewrite renameIdentity branch in Refl
  renameIdentity (PairValue annotation firstValue secondValue) =
    rewrite renameIdentity annotation in
    rewrite renameIdentity firstValue in
    rewrite renameIdentity secondValue in Refl
  renameIdentity (Pi q domain body) =
    rewrite renameIdentity domain in
    rewrite renameCongruent (liftRenaming Prelude.id) Prelude.id liftIdentity body in
    rewrite renameIdentity body in Refl
  renameIdentity (Sigma q r domain body) =
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
  renameIdentity (BoxValue function argument) =
    rewrite renameIdentity function in
    rewrite renameIdentity argument in Refl
  renameIdentity (StringEqual function argument) =
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
  renameComposition first second NatType = Refl
  renameComposition first second NatZero = Refl
  renameComposition first second (NatSucc x) = cong NatSucc (renameComposition first second x)
  renameComposition first second (NatRec p z s x) = rewrite renameComposition first second p in rewrite renameComposition first second z in rewrite renameComposition first second s in rewrite renameComposition first second x in Refl
  renameComposition first second (NatRecRuntime p z s x) = rewrite renameComposition first second p in rewrite renameComposition first second z in rewrite renameComposition first second s in rewrite renameComposition first second x in Refl
  renameComposition first second (RecType key) = Refl
  renameComposition first second (RecEnd ty) = cong RecEnd (renameComposition first second ty)
  renameComposition first second (RecMore ty x) = rewrite renameComposition first second ty in rewrite renameComposition first second x in Refl
  renameComposition first second (RecFold p z s x) = rewrite renameComposition first second p in rewrite renameComposition first second z in rewrite renameComposition first second s in rewrite renameComposition first second x in Refl
  renameComposition first second StringType = Refl
  renameComposition first second (StringValue _) = Refl
  renameComposition first second (IOType value) = cong IOType (renameComposition first second value)
  renameComposition first second (NominalType key indices shape) = rewrite renameCompositionTerms first second indices in rewrite renameComposition first second shape in Refl
  renameComposition first second (NominalValue ty value) = rewrite renameComposition first second ty in rewrite renameComposition first second value in Refl
  renameComposition first second (NominalCase motive value branch) = rewrite renameComposition first second motive in rewrite renameComposition first second value in rewrite renameComposition first second branch in Refl
  renameComposition first second (VariantType arms) = rewrite renameCompositionArms first second arms in Refl
  renameComposition first second (VariantValue ty tag Nothing) = rewrite renameComposition first second ty in Refl
  renameComposition first second (VariantValue ty tag (Just value)) = rewrite renameComposition first second ty in rewrite renameComposition first second value in Refl
  renameComposition first second (VariantCase motive value branches) = rewrite renameComposition first second motive in rewrite renameComposition first second value in rewrite renameCompositionTerms first second branches in Refl
  renameComposition first second (BoxType q value) = cong (BoxType q) (renameComposition first second value)
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
  renameComposition first second (PairCase motive scrutinee branch) =
    rewrite renameComposition first second motive in
    rewrite renameComposition first second scrutinee in
    rewrite renameComposition first second branch in Refl
  renameComposition first second (BoxCase motive scrutinee branch) =
    rewrite renameComposition first second motive in
    rewrite renameComposition first second scrutinee in
    rewrite renameComposition first second branch in Refl
  renameComposition first second (PairValue annotation firstValue secondValue) =
    rewrite renameComposition first second annotation in
    rewrite renameComposition first second firstValue in
    rewrite renameComposition first second secondValue in Refl
  renameComposition first second (Pi q domain body) =
    rewrite renameComposition first second domain in
    rewrite renameComposition (liftRenaming first) (liftRenaming second) body in
    rewrite renameCongruent (liftRenaming second . liftRenaming first)
                           (liftRenaming (second . first))
                           (liftComposition first second) body in Refl
  renameComposition first second (Sigma q r domain body) =
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
  renameComposition first second (BoxValue function argument) =
    rewrite renameComposition first second function in
    rewrite renameComposition first second argument in Refl
  renameComposition first second (StringEqual function argument) =
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


  renameCongruentArms : (left, right : Fin n -> Fin m) -> ((i : Fin n) -> left i = right i) -> (xs : List (Maybe (Quantity, Term n))) -> renameArms left xs = renameArms right xs
  renameCongruentArms left right agree [] = Refl
  renameCongruentArms left right agree (Nothing :: rest) = rewrite renameCongruentArms left right agree rest in Refl
  renameCongruentArms left right agree (Just (q, ty) :: rest) = rewrite renameCongruent left right agree ty in rewrite renameCongruentArms left right agree rest in Refl

  renameCongruentTerms : (left, right : Fin n -> Fin m) -> ((i : Fin n) -> left i = right i) -> (xs : List (Term n)) -> renameTerms left xs = renameTerms right xs
  renameCongruentTerms left right agree [] = Refl
  renameCongruentTerms left right agree (value :: rest) = rewrite renameCongruent left right agree value in rewrite renameCongruentTerms left right agree rest in Refl

  renameIdentityArms :  (xs : List (Maybe (Quantity, Term n))) -> renameArms Prelude.id xs = xs
  renameIdentityArms [] = Refl
  renameIdentityArms (Nothing :: rest) = rewrite renameIdentityArms rest in Refl
  renameIdentityArms (Just (q, ty) :: rest) = rewrite renameIdentity ty in rewrite renameIdentityArms rest in Refl

  renameIdentityTerms :  (xs : List (Term n)) -> renameTerms Prelude.id xs = xs
  renameIdentityTerms [] = Refl
  renameIdentityTerms (value :: rest) = rewrite renameIdentity value in rewrite renameIdentityTerms rest in Refl

  renameCompositionArms : (first : Fin n -> Fin m) -> (second : Fin m -> Fin k) -> (xs : List (Maybe (Quantity, Term n))) -> renameArms second (renameArms first xs) = renameArms (second . first) xs
  renameCompositionArms first second [] = Refl
  renameCompositionArms first second (Nothing :: rest) = rewrite renameCompositionArms first second rest in Refl
  renameCompositionArms first second (Just (q, ty) :: rest) = rewrite renameComposition first second ty in rewrite renameCompositionArms first second rest in Refl

  renameCompositionTerms : (first : Fin n -> Fin m) -> (second : Fin m -> Fin k) -> (xs : List (Term n)) -> renameTerms second (renameTerms first xs) = renameTerms (second . first) xs
  renameCompositionTerms first second [] = Refl
  renameCompositionTerms first second (value :: rest) = rewrite renameComposition first second value in rewrite renameCompositionTerms first second rest in Refl
