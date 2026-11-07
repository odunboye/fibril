module Fibril.Core.Quantitative.Usage

import Data.Vect
import Decidable.Equality
import Fibril.Core.Quantity
import Fibril.Core.Usage
import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Quantitative.Substitution

%default total

public export
variableDemand : {n : Nat} -> {0 context : Vect n Ty} -> Var context a -> Usage n
variableDemand Here = Linear :: zeroUsage
variableDemand (There variable) = Erased :: variableDemand variable

||| Quantitative derivations for this isolated syntax. No ambient validation is
||| required of subterms: siblings share permissions. Lambdas retain captures;
||| application scales demand; alternatives join, rather than sum, executions.
||| All arguments (even erased ones) must have internally valid derivations.
||| This deliberately stricter fragment is not a model of all Core.Runtime terms.
public export
data Uses : {n : Nat} -> {0 context : Vect n Ty} ->
            Term context a -> Usage n -> Type where
  UseRef : (variable : Var context a) -> Uses (Ref variable) (variableDemand variable)
  UseUnit : Uses Unit Fibril.Core.Usage.zeroUsage
  UseBoolean : Uses (Boolean value) Fibril.Core.Usage.zeroUsage
  UseLam : Uses body (used :: captures) -> allows q used = True ->
           Uses (Lam q body) captures
  UseApp : Uses function functionUsage -> Uses argument argumentUsage ->
           Uses (App {q} function argument)
                (combineUsage functionUsage (scaleUsage q argumentUsage))
  UseUnitElim : Uses value valueUsage -> Uses body bodyUsage ->
                Uses (UnitElim value body) (combineUsage valueUsage bodyUsage)
  UseIf : Uses condition conditionUsage -> Uses yes yesUsage -> Uses no noUsage ->
          Uses (If condition yes no)
               (combineUsage conditionUsage (joinUsage yesUsage noUsage))

||| Exact usage is uniquely determined by a term, independently of the
||| particular derivation. This does not prove substitution preservation.
public export
usageUnique : Uses term left -> Uses term right -> left = right
usageUnique (UseRef _) (UseRef _) = Refl
usageUnique UseUnit UseUnit = Refl
usageUnique UseBoolean UseBoolean = Refl
usageUnique (UseLam body _) (UseLam body' _) =
  case usageUnique body body' of Refl => Refl
usageUnique (UseApp fun arg) (UseApp fun' arg') =
  case usageUnique fun fun' of
    Refl => case usageUnique arg arg' of Refl => Refl
usageUnique (UseUnitElim value body) (UseUnitElim value' body') =
  case usageUnique value value' of
    Refl => case usageUnique body body' of Refl => Refl
usageUnique (UseIf condition yes no) (UseIf condition' yes' no') =
  case usageUnique condition condition' of
    Refl => case usageUnique yes yes' of
      Refl => case usageUnique no no' of Refl => Refl

||| Pointwise permission, NOT numerical ordering: Linear does not admit Erased.
public export
data Admits : Usage n -> Usage n -> Type where
  AdmitNil : Admits [] []
  AdmitCons : allows permission used = True -> Admits permissions usage ->
              Admits (permission :: permissions) (used :: usage)

||| Permissions admitting both branches admit their alternative join.
||| This lifts Quantity.joinAllows pointwise; it is not a term-substitution law.
public export
admitJoin : (permissions, left, right : Usage n) ->
            Admits permissions left -> Admits permissions right ->
            Admits permissions (joinUsage left right)
admitJoin [] [] [] AdmitNil AdmitNil = AdmitNil
admitJoin (permission :: permissions) (x :: xs) (y :: ys)
          (AdmitCons px restX) (AdmitCons py restY) =
  AdmitCons (rewrite joinAllows permission x y in rewrite px in py)
            (admitJoin permissions xs ys restX restY)

||| Left identity for the ambient demand vector in head-variable substitution.
public export
combineZeroLeft : (usage : Usage n) -> combineUsage Fibril.Core.Usage.zeroUsage usage = usage
combineZeroLeft [] = Refl
combineZeroLeft (q :: rest) = cong (q ::) (combineZeroLeft rest)

||| The head-reference case of single-linear substitution, with no restrictions
||| on the replacement beyond its derivation and the original ambient premise.
public export
instantiateHeadUsage : {n : Nat} -> {0 context : Vect n Ty} ->
  (value : Term context a) -> (w, permissions : Usage n) ->
  Uses value w -> Admits permissions (combineUsage Fibril.Core.Usage.zeroUsage w) ->
  (r : Usage n ** (Uses (instantiate value (Ref Here)) r, Admits permissions r))
instantiateHeadUsage value w permissions derivation admitted =
  (w ** (derivation, rewrite sym (combineZeroLeft w) in admitted))

public export
data UsageError
  = BinderMismatch Quantity Quantity
  | AmbientMismatch Nat Quantity Quantity

||| Success carries the actual derivation. This is not a substitution theorem,
||| an admission function for Core.Term, or a preservation result for reduction.
public export
inferUsage : {n : Nat} -> {0 context : Vect n Ty} -> (term : Term context a) ->
             Either UsageError (usage : Usage n ** Uses term usage)
inferUsage (Ref variable) = Right (variableDemand variable ** UseRef variable)
inferUsage Unit = Right (zeroUsage ** UseUnit)
inferUsage (Boolean value) = Right (zeroUsage ** UseBoolean)
inferUsage (Lam q body) = do
  (used :: captures ** derivation) <- inferUsage body
  case decEq (allows q used) True of
    Yes permitted => Right (captures ** UseLam derivation permitted)
    No _ => Left (BinderMismatch q used)
inferUsage (App {q} function argument) = do
  (functionUsage ** functionDerivation) <- inferUsage function
  (argumentUsage ** argumentDerivation) <- inferUsage argument
  Right (combineUsage functionUsage (scaleUsage q argumentUsage) **
         UseApp functionDerivation argumentDerivation)
inferUsage (UnitElim value body) = do
  (valueUsage ** valueDerivation) <- inferUsage value
  (bodyUsage ** bodyDerivation) <- inferUsage body
  Right (combineUsage valueUsage bodyUsage ** UseUnitElim valueDerivation bodyDerivation)
inferUsage (If condition yes no) = do
  (conditionUsage ** conditionDerivation) <- inferUsage condition
  (yesUsage ** yesDerivation) <- inferUsage yes
  (noUsage ** noDerivation) <- inferUsage no
  Right (combineUsage conditionUsage (joinUsage yesUsage noUsage) **
         UseIf conditionDerivation yesDerivation noDerivation)

public export
admitUsage : (permissions, usage : Usage n) -> Either UsageError (Admits permissions usage)
admitUsage [] [] = Right AdmitNil
admitUsage (permission :: permissions) (used :: usage) =
  case decEq (allows permission used) True of
    No _ => Left (AmbientMismatch 0 permission used)
    Yes permitted => case admitUsage permissions usage of
      Right rest => Right (AdmitCons permitted rest)
      Left (AmbientMismatch index expected observed) =>
        Left (AmbientMismatch (S index) expected observed)
      Left err => Left err

||| Validate ambient permissions only AFTER deriving the whole demand vector.
public export
checkUsage : {n : Nat} -> {0 context : Vect n Ty} -> (permissions : Usage n) -> (term : Term context a) ->
             Either UsageError (usage : Usage n ** (Uses term usage, Admits permissions usage))
checkUsage permissions term = do
  (usage ** derivation) <- inferUsage term
  permitted <- admitUsage permissions usage
  Right (usage ** (derivation, permitted))
