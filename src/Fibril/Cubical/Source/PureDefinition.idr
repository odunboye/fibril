module Fibril.Cubical.Source.PureDefinition

import Data.Fin
import Data.Vect
import Decidable.Equality
import Fibril.Core.Quantity
import Fibril.Core.Usage
import Fibril.Core.Term as C
import Fibril.Core.Quantitative.Syntax as Q
import Fibril.Core.Quantitative.CoreTranslation
import Fibril.Core.Quantitative.Usage
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Cubical.Logical.CommonAdmission

%default total

sameQuantity : (q, r : Quantity) -> Maybe (q = r)
sameQuantity Erased Erased = Just Refl
sameQuantity Linear Linear = Just Refl
sameQuantity Unrestricted Unrestricted = Just Refl
sameQuantity _ _ = Nothing

public export
samePureType : (a, b : Ty) -> Maybe (a = b)
samePureType UnitTy UnitTy = Just Refl
samePureType BoolTy BoolTy = Just Refl
samePureType (Arrow q a b) (Arrow r c d) = do
  Refl <- sameQuantity q r
  Refl <- samePureType a c
  Refl <- samePureType b d
  Just Refl
samePureType _ _ = Nothing

||| A constructive comparison of only the supported production constructors.
public export
samePureCore : (left, right : C.Term n) -> Maybe (left = right)
samePureCore (Variable i) (Variable j) = case decEq i j of
  Yes Refl => Just Refl
  No _ => Nothing
samePureCore UnitType UnitType = Just Refl
samePureCore BoolType BoolType = Just Refl
samePureCore UnitValue UnitValue = Just Refl
samePureCore BoolTrue BoolTrue = Just Refl
samePureCore BoolFalse BoolFalse = Just Refl
samePureCore (Pi q a b) (Pi r c d) = do
  Refl <- sameQuantity q r
  Refl <- samePureCore a c
  Refl <- samePureCore b d
  Just Refl
samePureCore (Lambda q a b) (Lambda r c d) = do
  Refl <- sameQuantity q r
  Refl <- samePureCore a c
  Refl <- samePureCore b d
  Just Refl
samePureCore (Apply f x) (Apply g y) = do
  Refl <- samePureCore f g
  Refl <- samePureCore x y
  Just Refl
samePureCore (UnitCase v b) (UnitCase w c) = do
  Refl <- samePureCore v w
  Refl <- samePureCore b c
  Just Refl
samePureCore (BoolCase c y z) (BoolCase d u v) = do
  Refl <- samePureCore c d
  Refl <- samePureCore y u
  Refl <- samePureCore z v
  Just Refl
samePureCore _ _ = Nothing

||| No conversion: even the nondependent codomain must be an exact type image.
public export
readPureType : Nat -> (raw : C.Term n) -> Maybe (ty : Ty ** coreType ty = raw)
readPureType Z _ = Nothing
readPureType (S fuel) UnitType = Just (UnitTy ** Refl)
readPureType (S fuel) BoolType = Just (BoolTy ** Refl)
readPureType (S fuel) (Pi Erased _ _) = Nothing
readPureType (S fuel) (Pi q domain body) = do
  (a ** Refl) <- readPureType fuel domain
  (b ** Refl) <- readPureType fuel body
  Just (Arrow q a b ** Refl)
readPureType _ _ = Nothing

variableAt : (ctx : Vect n Ty) -> (i : Fin n) ->
  (a : Ty ** v : Var ctx a ** coreVar v = i)
variableAt (a :: ctx) FZ = (a ** Here ** Refl)
variableAt (b :: ctx) (FS i) =
  let (a ** v ** exact) = variableAt ctx i in
    (a ** There v ** cong FS exact)

||| Exact re-embedding, not merely equal logical erasures. Quantities, domains,
||| variable positions and every production constructor are retained.
public export
record PureImage (ctx : Vect n Ty) (raw : C.Term n) where
  constructor Image
  ty : Ty
  pureTerm : Q.Term ctx ty
  annotations : Annotations pureTerm
  exactSource : coreTerm ty pureTerm annotations = raw

coreApplication : {0 ctx : Vect n Ty} -> (b, a : Ty) -> (q : Quantity) ->
  (f : Q.Term ctx (Arrow q a b)) -> (x : Q.Term ctx a) ->
  (fa : Annotations f) -> (xa : Annotations x) ->
  coreTerm b (App {q} f x) (AApp {q} a fa xa) = Apply (coreTerm (Arrow q a b) f fa) (coreTerm a x xa)
coreApplication UnitTy a q f x fa xa = Refl
coreApplication BoolTy a q f x fa xa = Refl
coreApplication (Arrow r b c) a q f x fa xa = Refl

coreElimination : {0 ctx : Vect n Ty} -> (a : Ty) -> (v : Q.Term ctx UnitTy) -> (b : Q.Term ctx a) ->
  (va : Annotations v) -> (ba : Annotations b) ->
  coreTerm a (UnitElim v b) (AUnitElim va ba) = UnitCase (coreTerm UnitTy v va) (coreTerm a b ba)
coreElimination UnitTy v b va ba = Refl
coreElimination BoolTy v b va ba = Refl
coreElimination (Arrow q a c) v b va ba = Refl

coreConditional : {0 ctx : Vect n Ty} -> (a : Ty) -> (c : Q.Term ctx BoolTy) -> (y, z : Q.Term ctx a) ->
  (ca : Annotations c) -> (ya : Annotations y) -> (za : Annotations z) ->
  coreTerm a (If c y z) (AIf ca ya za) = BoolCase (coreTerm BoolTy c ca) (coreTerm a y ya) (coreTerm a z za)
coreConditional UnitTy c y z ca ya za = Refl
coreConditional BoolTy c y z ca ya za = Refl
coreConditional (Arrow q a b) c y z ca ya za = Refl

public export
extractPure : Nat -> (ctx : Vect n Ty) -> (raw : C.Term n) -> Maybe (PureImage ctx raw)
extractPure Z _ _ = Nothing
extractPure (S fuel) ctx (Variable i) =
  let (a ** v ** exact) = variableAt ctx i in
    Just (Image a (Ref v) ARef (cong Variable exact))
extractPure (S fuel) ctx UnitValue = Just (Image UnitTy Unit AUnit Refl)
extractPure (S fuel) ctx BoolTrue = Just (Image BoolTy (Boolean True) ABoolean Refl)
extractPure (S fuel) ctx BoolFalse = Just (Image BoolTy (Boolean False) ABoolean Refl)
extractPure (S fuel) ctx (Lambda Erased _ _) = Nothing
extractPure (S fuel) ctx (Lambda q domain body) = do
  (a ** Refl) <- readPureType fuel domain
  Image b term ann Refl <- extractPure fuel (a :: ctx) body
  Just (Image (Arrow q a b) (Lam q term) (ALam ann) Refl)
extractPure (S fuel) ctx (Apply function argument) = do
  Image (Arrow q a b) fun fa Refl <- extractPure fuel ctx function
    | _ => Nothing
  Image c arg aa Refl <- extractPure fuel ctx argument
  Refl <- samePureType a c
  Just (Image b (App {q} fun arg) (AApp {q} a fa aa) (coreApplication b a q fun arg fa aa))
extractPure (S fuel) ctx (UnitCase value body) = do
  Image UnitTy val va Refl <- extractPure fuel ctx value
    | _ => Nothing
  Image a term ann Refl <- extractPure fuel ctx body
  Just (Image a (UnitElim val term) (AUnitElim va ann) (coreElimination a val term va ann))
extractPure (S fuel) ctx (BoolCase condition yes no) = do
  Image BoolTy cond ca Refl <- extractPure fuel ctx condition
    | _ => Nothing
  Image a left la Refl <- extractPure fuel ctx yes
  Image b right ra Refl <- extractPure fuel ctx no
  Refl <- samePureType a b
  Just (Image a (If cond left right) (AIf ca la ra) (coreConditional a cond left right ca la ra))
extractPure _ _ _ = Nothing

trueEvidence : (b : Bool) -> Maybe (b = True)
trueEvidence True = Just Refl
trueEvidence False = Nothing

||| Independently construct actual Uses, including internally valid arguments.
||| Production inferRuntime still checks the original complete application.
public export
pureUses : {n : Nat} -> {0 ctx : Vect n Ty} -> (term : Q.Term ctx a) -> Maybe (u : Usage n ** Uses term u)
pureUses (Ref v) = Just (variableDemand v ** UseRef v)
pureUses Unit = Just (zeroUsage ** UseUnit)
pureUses (Boolean b) = Just (zeroUsage ** UseBoolean)
pureUses (Lam q body) = do
  (used :: captures ** derivation) <- pureUses body
  allowed <- trueEvidence (allows q used)
  Just (captures ** UseLam derivation allowed)
pureUses (App {q} fun arg) = do
  (fu ** f) <- pureUses fun
  (au ** a) <- pureUses arg
  Just (combineUsage fu (scaleUsage q au) ** UseApp f a)
pureUses (UnitElim val body) = do
  (vu ** v) <- pureUses val
  (bu ** b) <- pureUses body
  Just (combineUsage vu bu ** UseUnitElim v b)
pureUses (If cond yes no) = do
  (cu ** c) <- pureUses cond
  (yu ** y) <- pureUses yes
  (nu ** n) <- pureUses no
  Just (combineUsage cu (joinUsage yu nu) ** UseIf c y n)

public export
pureAdmission : {0 ctx : Vect n Ty} -> (term : Q.Term ctx a) -> Annotations term -> AdmissionTerm n
pureAdmission (Ref v) ARef = AVar (coreVar v)
pureAdmission Unit AUnit = AUnit
pureAdmission (Boolean b) ABoolean = ABool b
pureAdmission (Lam q body) (ALam ann) = ALam (pureAdmission body ann)
pureAdmission (App fun arg) (AApp domain fa aa) =
  AApp (shadowType domain) (pureAdmission fun fa) (pureAdmission arg aa)
pureAdmission (UnitElim val body) (AUnitElim va ba) = AUnitElim (pureAdmission val va) (pureAdmission body ba)
pureAdmission (If cond yes no) (AIf ca ya na) = AIf (pureAdmission cond ca) (pureAdmission yes ya) (pureAdmission no na)

variableShadow : (v : Var ctx a) -> coreVar v = variableIndex (shadowVar v)
variableShadow Here = Refl
variableShadow (There v) = cong FS (variableShadow v)

||| Admission's erasure is the existing typed source shadow, at the same ctx/type.
public export
pureAdmissionShadow : {0 ctx : Vect n Ty} -> (term : Q.Term ctx a) -> (ann : Annotations term) ->
  eraseAdmission (pureAdmission term ann) = commonTerm (shadowTerm term)
pureAdmissionShadow (Ref v) ARef = cong CVar (variableShadow v)
pureAdmissionShadow Unit AUnit = Refl
pureAdmissionShadow (Boolean b) ABoolean = Refl
pureAdmissionShadow (Lam q body) (ALam ann) = cong CLam (pureAdmissionShadow body ann)
pureAdmissionShadow (App fun arg) (AApp domain fa aa) =
  rewrite pureAdmissionShadow fun fa in rewrite pureAdmissionShadow arg aa in Refl
pureAdmissionShadow (UnitElim val body) (AUnitElim va ba) =
  rewrite pureAdmissionShadow val va in rewrite pureAdmissionShadow body ba in Refl
pureAdmissionShadow (If cond yes no) (AIf ca ya na) =
  rewrite pureAdmissionShadow cond ca in rewrite pureAdmissionShadow yes ya in rewrite pureAdmissionShadow no na in Refl

public export
pureAdmissionTyped : {0 ctx : Vect n Ty} -> (term : Q.Term ctx a) -> (ann : Annotations term) ->
  CommonHasType (shadowContext ctx) (eraseAdmission (pureAdmission term ann)) (shadowType a)
pureAdmissionTyped term ann =
  rewrite pureAdmissionShadow term ann in commonTermTyped (shadowTerm term)
