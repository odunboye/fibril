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
  UseLam : {n : Nat} -> {0 context : Vect n Ty} -> {0 a, b : Ty} -> {0 body : Term (a :: context) b} -> {q : Quantity} -> {captures : Usage n} -> {used : Quantity} -> Uses body (used :: captures) -> allows q used = True ->
           Uses (Lam q body) captures
  UseApp : {n : Nat} -> {0 context : Vect n Ty} -> {0 a, b : Ty} -> {q : Quantity} -> {0 function : Term context (Arrow q a b)} -> {0 argument : Term context a} -> {functionUsage, argumentUsage : Usage n} -> Uses function functionUsage -> Uses argument argumentUsage ->
           Uses (App {q} function argument)
                (combineUsage functionUsage (scaleUsage q argumentUsage))
  UseUnitElim : {n : Nat} -> {0 context : Vect n Ty} -> {0 a : Ty} -> {0 value : Term context UnitTy} -> {0 body : Term context a} -> {valueUsage, bodyUsage : Usage n} -> Uses value valueUsage -> Uses body bodyUsage ->
                Uses (UnitElim value body) (combineUsage valueUsage bodyUsage)
  UseIf : {n : Nat} -> {0 context : Vect n Ty} -> {0 a : Ty} -> {0 condition : Term context BoolTy} -> {0 yes, no : Term context a} -> {conditionUsage, yesUsage, noUsage : Usage n} -> Uses condition conditionUsage -> Uses yes yesUsage -> Uses no noUsage ->
          Uses (If condition yes no)
               (combineUsage conditionUsage (joinUsage yesUsage noUsage))

||| Insert exactly one unused variable, possibly underneath retained binders.
public export
data Insertion : Vect n Ty -> Vect (S n) Ty -> Type where
  InsertHere : Insertion context (a :: context)
  InsertUnder : Insertion source target -> Insertion (a :: source) (a :: target)

public export
insertVariable : Insertion source target -> Renaming source target
insertVariable InsertHere = There
insertVariable (InsertUnder insertion) = liftRenaming (insertVariable insertion)

public export
insertDemand : {0 source : Vect n Ty} -> Insertion source target -> Usage n -> Usage (S n)
insertDemand InsertHere usage = Erased :: usage
insertDemand (InsertUnder insertion) (q :: usage) = q :: insertDemand insertion usage

insertZero : {0 source : Vect n Ty} -> (insertion : Insertion source target) ->
  insertDemand insertion Fibril.Core.Usage.zeroUsage = Fibril.Core.Usage.zeroUsage
insertZero InsertHere = Refl
insertZero (InsertUnder insertion) = cong (Erased ::) (insertZero insertion)

insertVariableDemand : {0 source : Vect n Ty} -> (insertion : Insertion source target) -> (variable : Var source a) ->
  variableDemand (insertVariable insertion variable) = insertDemand insertion (variableDemand variable)
insertVariableDemand InsertHere variable = Refl
insertVariableDemand (InsertUnder insertion) Here = cong (Linear ::) (sym (insertZero insertion))
insertVariableDemand (InsertUnder insertion) (There variable) =
  cong (Erased ::) (insertVariableDemand insertion variable)

insertCombine : {0 source : Vect n Ty} -> (insertion : Insertion source target) -> (left, right : Usage n) ->
  combineUsage (insertDemand insertion left) (insertDemand insertion right) =
  insertDemand insertion (combineUsage left right)
insertCombine InsertHere left right = Refl
insertCombine (InsertUnder insertion) (x :: xs) (y :: ys) =
  cong (add x y ::) (insertCombine insertion xs ys)

insertScale : {0 source : Vect n Ty} -> (insertion : Insertion source target) -> (q : Quantity) -> (usage : Usage n) ->
  scaleUsage q (insertDemand insertion usage) = insertDemand insertion (scaleUsage q usage)
insertScale InsertHere Erased usage = Refl
insertScale InsertHere Linear usage = Refl
insertScale InsertHere Unrestricted usage = Refl
insertScale (InsertUnder insertion) q (x :: xs) =
  cong (multiply q x ::) (insertScale insertion q xs)

insertJoin : {0 source : Vect n Ty} -> (insertion : Insertion source target) -> (left, right : Usage n) ->
  joinUsage (insertDemand insertion left) (insertDemand insertion right) =
  insertDemand insertion (joinUsage left right)
insertJoin InsertHere left right = Refl
insertJoin (InsertUnder insertion) (x :: xs) (y :: ys) =
  cong (joinQuantity x y ::) (insertJoin insertion xs ys)

||| Inserting one unused resource preserves the exact derivation, including
||| binders and all subderivations of erased arguments and alternatives.
public export
insertUses : {0 source : Vect n Ty} -> (insertion : Insertion source target) -> (term : Term source a) ->
  (usage : Usage n) -> Uses term usage ->
  Uses (rename (insertVariable insertion) term) (insertDemand insertion usage)
insertUses insertion (Ref variable) _ (UseRef _) =
  rewrite sym (insertVariableDemand insertion variable) in UseRef (insertVariable insertion variable)
insertUses insertion Unit _ UseUnit = rewrite insertZero insertion in UseUnit
insertUses insertion (Boolean value) _ UseBoolean = rewrite insertZero insertion in UseBoolean
insertUses insertion (Lam q body) captures (UseLam {used} derivation permitted) =
  UseLam (insertUses (InsertUnder insertion) body (used :: captures) derivation) permitted
insertUses insertion (App {q} function argument) _ (UseApp {functionUsage} {argumentUsage} fun arg) =
  rewrite sym (insertCombine insertion functionUsage (scaleUsage q argumentUsage)) in
  rewrite sym (insertScale insertion q argumentUsage) in
  UseApp (insertUses insertion function functionUsage fun) (insertUses insertion argument argumentUsage arg)
insertUses insertion (UnitElim value body) _ (UseUnitElim {valueUsage} {bodyUsage} val bod) =
  rewrite sym (insertCombine insertion valueUsage bodyUsage) in
  UseUnitElim (insertUses insertion value valueUsage val) (insertUses insertion body bodyUsage bod)
insertUses insertion (If condition yes no) _ (UseIf {conditionUsage} {yesUsage} {noUsage} cond y n) =
  rewrite sym (insertCombine insertion conditionUsage (joinUsage yesUsage noUsage)) in
  rewrite sym (insertJoin insertion yesUsage noUsage) in
  UseIf (insertUses insertion condition conditionUsage cond)
        (insertUses insertion yes yesUsage y) (insertUses insertion no noUsage n)

public export
weakenUses : (term : Term context a) -> (usage : Usage n) -> Uses term usage ->
             Uses (weaken {b} term) (Erased :: usage)
weakenUses term usage derivation = insertUses InsertHere term usage derivation

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

||| The permission preorder is oriented from actual demand to its bound.
public export
DemandLeq : Quantity -> Quantity -> Type
DemandLeq actual bound = allows bound actual = True

public export
demandRefl : (q : Quantity) -> DemandLeq q q
demandRefl Erased = Refl
demandRefl Linear = Refl
demandRefl Unrestricted = Refl

public export
demandTrans : (a, b, c : Quantity) -> DemandLeq a b -> DemandLeq b c -> DemandLeq a c
demandTrans Erased Erased Erased _ _ = Refl
demandTrans Erased Erased Unrestricted _ _ = Refl
demandTrans Erased Unrestricted Unrestricted _ _ = Refl
demandTrans Linear Linear Linear _ _ = Refl
demandTrans Linear Linear Unrestricted _ _ = Refl
demandTrans Linear Unrestricted Unrestricted _ _ = Refl
demandTrans Unrestricted Unrestricted Unrestricted _ _ = Refl

public export
addMonotone : (a, b, c, d : Quantity) -> DemandLeq a b -> DemandLeq c d -> DemandLeq (add a c) (add b d)
addMonotone Erased Erased Erased Erased _ _ = Refl
addMonotone Erased Erased Erased Unrestricted _ _ = Refl
addMonotone Erased Erased Linear Linear _ _ = Refl
addMonotone Erased Erased Linear Unrestricted _ _ = Refl
addMonotone Erased Erased Unrestricted Unrestricted _ _ = Refl
addMonotone Erased Unrestricted Erased Erased _ _ = Refl
addMonotone Erased Unrestricted Erased Unrestricted _ _ = Refl
addMonotone Erased Unrestricted Linear Linear _ _ = Refl
addMonotone Erased Unrestricted Linear Unrestricted _ _ = Refl
addMonotone Erased Unrestricted Unrestricted Unrestricted _ _ = Refl
addMonotone Linear Linear Erased Erased _ _ = Refl
addMonotone Linear Linear Erased Unrestricted _ _ = Refl
addMonotone Linear Linear Linear Linear _ _ = Refl
addMonotone Linear Linear Linear Unrestricted _ _ = Refl
addMonotone Linear Linear Unrestricted Unrestricted _ _ = Refl
addMonotone Linear Unrestricted Erased Erased _ _ = Refl
addMonotone Linear Unrestricted Erased Unrestricted _ _ = Refl
addMonotone Linear Unrestricted Linear Linear _ _ = Refl
addMonotone Linear Unrestricted Linear Unrestricted _ _ = Refl
addMonotone Linear Unrestricted Unrestricted Unrestricted _ _ = Refl
addMonotone Unrestricted Unrestricted Erased Erased _ _ = Refl
addMonotone Unrestricted Unrestricted Erased Unrestricted _ _ = Refl
addMonotone Unrestricted Unrestricted Linear Linear _ _ = Refl
addMonotone Unrestricted Unrestricted Linear Unrestricted _ _ = Refl
addMonotone Unrestricted Unrestricted Unrestricted Unrestricted _ _ = Refl

public export
multiplyMonotone : (a, b, c, d : Quantity) -> DemandLeq a b -> DemandLeq c d -> DemandLeq (multiply a c) (multiply b d)
multiplyMonotone Erased Erased Erased Erased _ _ = Refl
multiplyMonotone Erased Erased Erased Unrestricted _ _ = Refl
multiplyMonotone Erased Erased Linear Linear _ _ = Refl
multiplyMonotone Erased Erased Linear Unrestricted _ _ = Refl
multiplyMonotone Erased Erased Unrestricted Unrestricted _ _ = Refl
multiplyMonotone Erased Unrestricted Erased Erased _ _ = Refl
multiplyMonotone Erased Unrestricted Erased Unrestricted _ _ = Refl
multiplyMonotone Erased Unrestricted Linear Linear _ _ = Refl
multiplyMonotone Erased Unrestricted Linear Unrestricted _ _ = Refl
multiplyMonotone Erased Unrestricted Unrestricted Unrestricted _ _ = Refl
multiplyMonotone Linear Linear Erased Erased _ _ = Refl
multiplyMonotone Linear Linear Erased Unrestricted _ _ = Refl
multiplyMonotone Linear Linear Linear Linear _ _ = Refl
multiplyMonotone Linear Linear Linear Unrestricted _ _ = Refl
multiplyMonotone Linear Linear Unrestricted Unrestricted _ _ = Refl
multiplyMonotone Linear Unrestricted Erased Erased _ _ = Refl
multiplyMonotone Linear Unrestricted Erased Unrestricted _ _ = Refl
multiplyMonotone Linear Unrestricted Linear Linear _ _ = Refl
multiplyMonotone Linear Unrestricted Linear Unrestricted _ _ = Refl
multiplyMonotone Linear Unrestricted Unrestricted Unrestricted _ _ = Refl
multiplyMonotone Unrestricted Unrestricted Erased Erased _ _ = Refl
multiplyMonotone Unrestricted Unrestricted Erased Unrestricted _ _ = Refl
multiplyMonotone Unrestricted Unrestricted Linear Linear _ _ = Refl
multiplyMonotone Unrestricted Unrestricted Linear Unrestricted _ _ = Refl
multiplyMonotone Unrestricted Unrestricted Unrestricted Unrestricted _ _ = Refl

public export
joinMonotone : (a, b, c, d : Quantity) -> DemandLeq a b -> DemandLeq c d -> DemandLeq (joinQuantity a c) (joinQuantity b d)
joinMonotone Erased Erased Erased Erased _ _ = Refl
joinMonotone Erased Erased Erased Unrestricted _ _ = Refl
joinMonotone Erased Erased Linear Linear _ _ = Refl
joinMonotone Erased Erased Linear Unrestricted _ _ = Refl
joinMonotone Erased Erased Unrestricted Unrestricted _ _ = Refl
joinMonotone Erased Unrestricted Erased Erased _ _ = Refl
joinMonotone Erased Unrestricted Erased Unrestricted _ _ = Refl
joinMonotone Erased Unrestricted Linear Linear _ _ = Refl
joinMonotone Erased Unrestricted Linear Unrestricted _ _ = Refl
joinMonotone Erased Unrestricted Unrestricted Unrestricted _ _ = Refl
joinMonotone Linear Linear Erased Erased _ _ = Refl
joinMonotone Linear Linear Erased Unrestricted _ _ = Refl
joinMonotone Linear Linear Linear Linear _ _ = Refl
joinMonotone Linear Linear Linear Unrestricted _ _ = Refl
joinMonotone Linear Linear Unrestricted Unrestricted _ _ = Refl
joinMonotone Linear Unrestricted Erased Erased _ _ = Refl
joinMonotone Linear Unrestricted Erased Unrestricted _ _ = Refl
joinMonotone Linear Unrestricted Linear Linear _ _ = Refl
joinMonotone Linear Unrestricted Linear Unrestricted _ _ = Refl
joinMonotone Linear Unrestricted Unrestricted Unrestricted _ _ = Refl
joinMonotone Unrestricted Unrestricted Erased Erased _ _ = Refl
joinMonotone Unrestricted Unrestricted Erased Unrestricted _ _ = Refl
joinMonotone Unrestricted Unrestricted Linear Linear _ _ = Refl
joinMonotone Unrestricted Unrestricted Linear Unrestricted _ _ = Refl
joinMonotone Unrestricted Unrestricted Unrestricted Unrestricted _ _ = Refl

public export
joinUpperLeft : (a, b : Quantity) -> DemandLeq a (joinQuantity a b)
joinUpperLeft Erased Erased = Refl
joinUpperLeft Erased Linear = Refl
joinUpperLeft Erased Unrestricted = Refl
joinUpperLeft Linear Erased = Refl
joinUpperLeft Linear Linear = Refl
joinUpperLeft Linear Unrestricted = Refl
joinUpperLeft Unrestricted Erased = Refl
joinUpperLeft Unrestricted Linear = Refl
joinUpperLeft Unrestricted Unrestricted = Refl

public export
joinUpperRight : (a, b : Quantity) -> DemandLeq b (joinQuantity a b)
joinUpperRight Erased Erased = Refl
joinUpperRight Erased Linear = Refl
joinUpperRight Erased Unrestricted = Refl
joinUpperRight Linear Erased = Refl
joinUpperRight Linear Linear = Refl
joinUpperRight Linear Unrestricted = Refl
joinUpperRight Unrestricted Erased = Refl
joinUpperRight Unrestricted Linear = Refl
joinUpperRight Unrestricted Unrestricted = Refl

||| Admits is the pointwise lifting of DemandLeq with arguments reversed.
public export
admitTrans : (bounds, middle, actual : Usage n) -> Admits bounds middle -> Admits middle actual -> Admits bounds actual
admitTrans [] [] [] AdmitNil AdmitNil = AdmitNil
admitTrans (bound :: bounds) (mid :: middle) (actual :: rest) (AdmitCons p ps) (AdmitCons q qs) =
  AdmitCons (demandTrans actual mid bound q p) (admitTrans bounds middle rest ps qs)

public export
combineMonotone : (a, b, c, d : Usage n) -> Admits b a -> Admits d c ->
  Admits (combineUsage b d) (combineUsage a c)
combineMonotone [] [] [] [] AdmitNil AdmitNil = AdmitNil
combineMonotone (a :: as) (b :: bs) (c :: cs) (d :: ds) (AdmitCons p ps) (AdmitCons q qs) =
  AdmitCons (addMonotone a b c d p q) (combineMonotone as bs cs ds ps qs)

public export
scaleMonotone : (q, r : Quantity) -> (a, b : Usage n) -> DemandLeq q r -> Admits b a ->
  Admits (scaleUsage r b) (scaleUsage q a)
scaleMonotone q r [] [] qr AdmitNil = AdmitNil
scaleMonotone q r (a :: as) (b :: bs) qr (AdmitCons p ps) =
  AdmitCons (multiplyMonotone q r a b qr p) (scaleMonotone q r as bs qr ps)

public export
joinMonotoneUsage : (a, b, c, d : Usage n) -> Admits b a -> Admits d c ->
  Admits (joinUsage b d) (joinUsage a c)
joinMonotoneUsage [] [] [] [] AdmitNil AdmitNil = AdmitNil
joinMonotoneUsage (a :: as) (b :: bs) (c :: cs) (d :: ds) (AdmitCons p ps) (AdmitCons q qs) =
  AdmitCons (joinMonotone a b c d p q) (joinMonotoneUsage as bs cs ds ps qs)

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

||| Adding the same demand to each alternative commutes with permission join.
||| This is specific to the three Fibril quantities and their exact join.
public export
addJoinCommon : (left, right, common : Quantity) ->
  add (joinQuantity left right) common =
  joinQuantity (add left common) (add right common)
addJoinCommon Erased Erased Erased = Refl
addJoinCommon Erased Erased Linear = Refl
addJoinCommon Erased Erased Unrestricted = Refl
addJoinCommon Erased Linear Erased = Refl
addJoinCommon Erased Linear Linear = Refl
addJoinCommon Erased Linear Unrestricted = Refl
addJoinCommon Erased Unrestricted Erased = Refl
addJoinCommon Erased Unrestricted Linear = Refl
addJoinCommon Erased Unrestricted Unrestricted = Refl
addJoinCommon Linear Erased Erased = Refl
addJoinCommon Linear Erased Linear = Refl
addJoinCommon Linear Erased Unrestricted = Refl
addJoinCommon Linear Linear Erased = Refl
addJoinCommon Linear Linear Linear = Refl
addJoinCommon Linear Linear Unrestricted = Refl
addJoinCommon Linear Unrestricted Erased = Refl
addJoinCommon Linear Unrestricted Linear = Refl
addJoinCommon Linear Unrestricted Unrestricted = Refl
addJoinCommon Unrestricted Erased Erased = Refl
addJoinCommon Unrestricted Erased Linear = Refl
addJoinCommon Unrestricted Erased Unrestricted = Refl
addJoinCommon Unrestricted Linear Erased = Refl
addJoinCommon Unrestricted Linear Linear = Refl
addJoinCommon Unrestricted Linear Unrestricted = Refl
addJoinCommon Unrestricted Unrestricted Erased = Refl
addJoinCommon Unrestricted Unrestricted Linear = Refl
addJoinCommon Unrestricted Unrestricted Unrestricted = Refl

||| Pointwise common-replacement demand can be moved through alternatives.
||| No claim is made when the replacement is charged differently per branch.
public export
combineJoinCommon : (left, right, common : Usage n) ->
  combineUsage (joinUsage left right) common =
  joinUsage (combineUsage left common) (combineUsage right common)
combineJoinCommon [] [] [] = Refl
combineJoinCommon (x :: xs) (y :: ys) (z :: zs) =
  rewrite addJoinCommon x y z in
  cong (joinQuantity (add x z) (add y z) ::) (combineJoinCommon xs ys zs)

andTrueLeft : (x, y : Bool) -> x && y = True -> x = True
andTrueLeft False _ Refl impossible
andTrueLeft True _ _ = Refl

andTrueRight : (x, y : Bool) -> x && y = True -> y = True
andTrueRight False _ Refl impossible
andTrueRight True _ prf = prf

||| Each alternative is admitted whenever their exact permission join is.
public export
admitJoinParts : (permissions, left, right : Usage n) ->
  Admits permissions (joinUsage left right) ->
  (Admits permissions left, Admits permissions right)
admitJoinParts [] [] [] AdmitNil = (AdmitNil, AdmitNil)
admitJoinParts (p :: ps) (x :: xs) (y :: ys) (AdmitCons allowed rest) =
  let (left, right) = admitJoinParts ps xs ys rest in
  case joinAllows p x y of
    equality => case trans (sym equality) allowed of
      both => (AdmitCons (andTrueLeft (allows p x) (allows p y) both) left,
               AdmitCons (andTrueRight (allows p x) (allows p y) both) right)

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

||| Joining the same exact demand in two alternatives preserves it. This is
||| alternative sharing, not sequential duplication of a linear resource.
public export
joinUsageIdempotent : (usage : Usage n) -> joinUsage usage usage = usage
joinUsageIdempotent [] = Refl
joinUsageIdempotent (Erased :: rest) = cong (Erased ::) (joinUsageIdempotent rest)
joinUsageIdempotent (Linear :: rest) = cong (Linear ::) (joinUsageIdempotent rest)
joinUsageIdempotent (Unrestricted :: rest) = cong (Unrestricted ::) (joinUsageIdempotent rest)

||| Substitution into either occurrence of a head reference in alternatives:
||| both syntactic copies share the same ambient demand, including linear uses.
public export
instantiateAlternativesUsage : {n : Nat} -> {0 context : Vect n Ty} ->
  (value : Term context a) -> (flag : Bool) -> (w, permissions : Usage n) ->
  Uses value w -> Admits permissions w ->
  (r : Usage n **
    (Uses (instantiate value (If (Boolean flag) (Ref Here) (Ref Here))) r,
     Admits permissions r))
instantiateAlternativesUsage value flag w permissions derivation admitted =
  (w ** (rewrite sym (combineZeroLeft w) in
          rewrite sym (joinUsageIdempotent w) in
          UseIf UseBoolean derivation derivation, admitted))

||| Project the deleted coefficient and retained vector along a single-substitution path.
public export
deletedDemand : {0 source : Vect (S n) Ty} -> {0 target : Vect n Ty} -> (substitution : SingleSubstitution source target) -> Usage (S n) -> Quantity
deletedDemand (SubstituteHere _) (q :: rest) = q
deletedDemand (SubstituteUnder substitution) (q :: rest) = deletedDemand substitution rest

public export
retainedDemand : {0 source : Vect (S n) Ty} -> {0 target : Vect n Ty} -> (substitution : SingleSubstitution source target) -> Usage (S n) -> Usage n
retainedDemand (SubstituteHere _) (q :: rest) = rest
retainedDemand (SubstituteUnder substitution) (q :: rest) = q :: retainedDemand substitution rest

||| Splitting a sequential source demand commutes with pointwise addition.
public export
retainedCombine : {0 source : Vect (S n) Ty} -> {0 target : Vect n Ty} ->
  (substitution : SingleSubstitution source target) -> (left, right : Usage (S n)) ->
  retainedDemand substitution (combineUsage left right) =
    combineUsage (retainedDemand substitution left) (retainedDemand substitution right)
retainedCombine (SubstituteHere _) (x :: xs) (y :: ys) = Refl
retainedCombine (SubstituteUnder substitution) (x :: xs) (y :: ys) =
  cong (add x y ::) (retainedCombine substitution xs ys)

public export
deletedCombine : {0 source : Vect (S n) Ty} -> {0 target : Vect n Ty} ->
  (substitution : SingleSubstitution source target) -> (left, right : Usage (S n)) ->
  deletedDemand substitution (combineUsage left right) =
    add (deletedDemand substitution left) (deletedDemand substitution right)
deletedCombine (SubstituteHere _) (x :: xs) (y :: ys) = Refl
deletedCombine (SubstituteUnder substitution) (x :: xs) (y :: ys) =
  deletedCombine substitution xs ys

||| A replacement's ambient demand is zero at each retained prefix variable.
public export
replacementDemand : {0 source : Vect (S n) Ty} -> {0 target : Vect n Ty} -> (substitution : SingleSubstitution source target) -> Usage n -> Usage n
replacementDemand (SubstituteHere _) usage = usage
replacementDemand (SubstituteUnder substitution) (q :: rest) = Erased :: replacementDemand substitution rest

||| Sequential composition distributes the replacement charge over two uses.
public export
substitutionAddInterchange : (a, b, c, d, w : Quantity) ->
  add (add a (multiply b w)) (add c (multiply d w)) =
  add (add a c) (multiply (add b d) w)
substitutionAddInterchange Erased Erased Erased Erased Erased = Refl
substitutionAddInterchange Erased Erased Erased Erased Linear = Refl
substitutionAddInterchange Erased Erased Erased Erased Unrestricted = Refl
substitutionAddInterchange Erased Erased Erased Linear Erased = Refl
substitutionAddInterchange Erased Erased Erased Linear Linear = Refl
substitutionAddInterchange Erased Erased Erased Linear Unrestricted = Refl
substitutionAddInterchange Erased Erased Erased Unrestricted Erased = Refl
substitutionAddInterchange Erased Erased Erased Unrestricted Linear = Refl
substitutionAddInterchange Erased Erased Erased Unrestricted Unrestricted = Refl
substitutionAddInterchange Erased Erased Linear Erased Erased = Refl
substitutionAddInterchange Erased Erased Linear Erased Linear = Refl
substitutionAddInterchange Erased Erased Linear Erased Unrestricted = Refl
substitutionAddInterchange Erased Erased Linear Linear Erased = Refl
substitutionAddInterchange Erased Erased Linear Linear Linear = Refl
substitutionAddInterchange Erased Erased Linear Linear Unrestricted = Refl
substitutionAddInterchange Erased Erased Linear Unrestricted Erased = Refl
substitutionAddInterchange Erased Erased Linear Unrestricted Linear = Refl
substitutionAddInterchange Erased Erased Linear Unrestricted Unrestricted = Refl
substitutionAddInterchange Erased Erased Unrestricted Erased Erased = Refl
substitutionAddInterchange Erased Erased Unrestricted Erased Linear = Refl
substitutionAddInterchange Erased Erased Unrestricted Erased Unrestricted = Refl
substitutionAddInterchange Erased Erased Unrestricted Linear Erased = Refl
substitutionAddInterchange Erased Erased Unrestricted Linear Linear = Refl
substitutionAddInterchange Erased Erased Unrestricted Linear Unrestricted = Refl
substitutionAddInterchange Erased Erased Unrestricted Unrestricted Erased = Refl
substitutionAddInterchange Erased Erased Unrestricted Unrestricted Linear = Refl
substitutionAddInterchange Erased Erased Unrestricted Unrestricted Unrestricted = Refl
substitutionAddInterchange Erased Linear Erased Erased Erased = Refl
substitutionAddInterchange Erased Linear Erased Erased Linear = Refl
substitutionAddInterchange Erased Linear Erased Erased Unrestricted = Refl
substitutionAddInterchange Erased Linear Erased Linear Erased = Refl
substitutionAddInterchange Erased Linear Erased Linear Linear = Refl
substitutionAddInterchange Erased Linear Erased Linear Unrestricted = Refl
substitutionAddInterchange Erased Linear Erased Unrestricted Erased = Refl
substitutionAddInterchange Erased Linear Erased Unrestricted Linear = Refl
substitutionAddInterchange Erased Linear Erased Unrestricted Unrestricted = Refl
substitutionAddInterchange Erased Linear Linear Erased Erased = Refl
substitutionAddInterchange Erased Linear Linear Erased Linear = Refl
substitutionAddInterchange Erased Linear Linear Erased Unrestricted = Refl
substitutionAddInterchange Erased Linear Linear Linear Erased = Refl
substitutionAddInterchange Erased Linear Linear Linear Linear = Refl
substitutionAddInterchange Erased Linear Linear Linear Unrestricted = Refl
substitutionAddInterchange Erased Linear Linear Unrestricted Erased = Refl
substitutionAddInterchange Erased Linear Linear Unrestricted Linear = Refl
substitutionAddInterchange Erased Linear Linear Unrestricted Unrestricted = Refl
substitutionAddInterchange Erased Linear Unrestricted Erased Erased = Refl
substitutionAddInterchange Erased Linear Unrestricted Erased Linear = Refl
substitutionAddInterchange Erased Linear Unrestricted Erased Unrestricted = Refl
substitutionAddInterchange Erased Linear Unrestricted Linear Erased = Refl
substitutionAddInterchange Erased Linear Unrestricted Linear Linear = Refl
substitutionAddInterchange Erased Linear Unrestricted Linear Unrestricted = Refl
substitutionAddInterchange Erased Linear Unrestricted Unrestricted Erased = Refl
substitutionAddInterchange Erased Linear Unrestricted Unrestricted Linear = Refl
substitutionAddInterchange Erased Linear Unrestricted Unrestricted Unrestricted = Refl
substitutionAddInterchange Erased Unrestricted Erased Erased Erased = Refl
substitutionAddInterchange Erased Unrestricted Erased Erased Linear = Refl
substitutionAddInterchange Erased Unrestricted Erased Erased Unrestricted = Refl
substitutionAddInterchange Erased Unrestricted Erased Linear Erased = Refl
substitutionAddInterchange Erased Unrestricted Erased Linear Linear = Refl
substitutionAddInterchange Erased Unrestricted Erased Linear Unrestricted = Refl
substitutionAddInterchange Erased Unrestricted Erased Unrestricted Erased = Refl
substitutionAddInterchange Erased Unrestricted Erased Unrestricted Linear = Refl
substitutionAddInterchange Erased Unrestricted Erased Unrestricted Unrestricted = Refl
substitutionAddInterchange Erased Unrestricted Linear Erased Erased = Refl
substitutionAddInterchange Erased Unrestricted Linear Erased Linear = Refl
substitutionAddInterchange Erased Unrestricted Linear Erased Unrestricted = Refl
substitutionAddInterchange Erased Unrestricted Linear Linear Erased = Refl
substitutionAddInterchange Erased Unrestricted Linear Linear Linear = Refl
substitutionAddInterchange Erased Unrestricted Linear Linear Unrestricted = Refl
substitutionAddInterchange Erased Unrestricted Linear Unrestricted Erased = Refl
substitutionAddInterchange Erased Unrestricted Linear Unrestricted Linear = Refl
substitutionAddInterchange Erased Unrestricted Linear Unrestricted Unrestricted = Refl
substitutionAddInterchange Erased Unrestricted Unrestricted Erased Erased = Refl
substitutionAddInterchange Erased Unrestricted Unrestricted Erased Linear = Refl
substitutionAddInterchange Erased Unrestricted Unrestricted Erased Unrestricted = Refl
substitutionAddInterchange Erased Unrestricted Unrestricted Linear Erased = Refl
substitutionAddInterchange Erased Unrestricted Unrestricted Linear Linear = Refl
substitutionAddInterchange Erased Unrestricted Unrestricted Linear Unrestricted = Refl
substitutionAddInterchange Erased Unrestricted Unrestricted Unrestricted Erased = Refl
substitutionAddInterchange Erased Unrestricted Unrestricted Unrestricted Linear = Refl
substitutionAddInterchange Erased Unrestricted Unrestricted Unrestricted Unrestricted = Refl
substitutionAddInterchange Linear Erased Erased Erased Erased = Refl
substitutionAddInterchange Linear Erased Erased Erased Linear = Refl
substitutionAddInterchange Linear Erased Erased Erased Unrestricted = Refl
substitutionAddInterchange Linear Erased Erased Linear Erased = Refl
substitutionAddInterchange Linear Erased Erased Linear Linear = Refl
substitutionAddInterchange Linear Erased Erased Linear Unrestricted = Refl
substitutionAddInterchange Linear Erased Erased Unrestricted Erased = Refl
substitutionAddInterchange Linear Erased Erased Unrestricted Linear = Refl
substitutionAddInterchange Linear Erased Erased Unrestricted Unrestricted = Refl
substitutionAddInterchange Linear Erased Linear Erased Erased = Refl
substitutionAddInterchange Linear Erased Linear Erased Linear = Refl
substitutionAddInterchange Linear Erased Linear Erased Unrestricted = Refl
substitutionAddInterchange Linear Erased Linear Linear Erased = Refl
substitutionAddInterchange Linear Erased Linear Linear Linear = Refl
substitutionAddInterchange Linear Erased Linear Linear Unrestricted = Refl
substitutionAddInterchange Linear Erased Linear Unrestricted Erased = Refl
substitutionAddInterchange Linear Erased Linear Unrestricted Linear = Refl
substitutionAddInterchange Linear Erased Linear Unrestricted Unrestricted = Refl
substitutionAddInterchange Linear Erased Unrestricted Erased Erased = Refl
substitutionAddInterchange Linear Erased Unrestricted Erased Linear = Refl
substitutionAddInterchange Linear Erased Unrestricted Erased Unrestricted = Refl
substitutionAddInterchange Linear Erased Unrestricted Linear Erased = Refl
substitutionAddInterchange Linear Erased Unrestricted Linear Linear = Refl
substitutionAddInterchange Linear Erased Unrestricted Linear Unrestricted = Refl
substitutionAddInterchange Linear Erased Unrestricted Unrestricted Erased = Refl
substitutionAddInterchange Linear Erased Unrestricted Unrestricted Linear = Refl
substitutionAddInterchange Linear Erased Unrestricted Unrestricted Unrestricted = Refl
substitutionAddInterchange Linear Linear Erased Erased Erased = Refl
substitutionAddInterchange Linear Linear Erased Erased Linear = Refl
substitutionAddInterchange Linear Linear Erased Erased Unrestricted = Refl
substitutionAddInterchange Linear Linear Erased Linear Erased = Refl
substitutionAddInterchange Linear Linear Erased Linear Linear = Refl
substitutionAddInterchange Linear Linear Erased Linear Unrestricted = Refl
substitutionAddInterchange Linear Linear Erased Unrestricted Erased = Refl
substitutionAddInterchange Linear Linear Erased Unrestricted Linear = Refl
substitutionAddInterchange Linear Linear Erased Unrestricted Unrestricted = Refl
substitutionAddInterchange Linear Linear Linear Erased Erased = Refl
substitutionAddInterchange Linear Linear Linear Erased Linear = Refl
substitutionAddInterchange Linear Linear Linear Erased Unrestricted = Refl
substitutionAddInterchange Linear Linear Linear Linear Erased = Refl
substitutionAddInterchange Linear Linear Linear Linear Linear = Refl
substitutionAddInterchange Linear Linear Linear Linear Unrestricted = Refl
substitutionAddInterchange Linear Linear Linear Unrestricted Erased = Refl
substitutionAddInterchange Linear Linear Linear Unrestricted Linear = Refl
substitutionAddInterchange Linear Linear Linear Unrestricted Unrestricted = Refl
substitutionAddInterchange Linear Linear Unrestricted Erased Erased = Refl
substitutionAddInterchange Linear Linear Unrestricted Erased Linear = Refl
substitutionAddInterchange Linear Linear Unrestricted Erased Unrestricted = Refl
substitutionAddInterchange Linear Linear Unrestricted Linear Erased = Refl
substitutionAddInterchange Linear Linear Unrestricted Linear Linear = Refl
substitutionAddInterchange Linear Linear Unrestricted Linear Unrestricted = Refl
substitutionAddInterchange Linear Linear Unrestricted Unrestricted Erased = Refl
substitutionAddInterchange Linear Linear Unrestricted Unrestricted Linear = Refl
substitutionAddInterchange Linear Linear Unrestricted Unrestricted Unrestricted = Refl
substitutionAddInterchange Linear Unrestricted Erased Erased Erased = Refl
substitutionAddInterchange Linear Unrestricted Erased Erased Linear = Refl
substitutionAddInterchange Linear Unrestricted Erased Erased Unrestricted = Refl
substitutionAddInterchange Linear Unrestricted Erased Linear Erased = Refl
substitutionAddInterchange Linear Unrestricted Erased Linear Linear = Refl
substitutionAddInterchange Linear Unrestricted Erased Linear Unrestricted = Refl
substitutionAddInterchange Linear Unrestricted Erased Unrestricted Erased = Refl
substitutionAddInterchange Linear Unrestricted Erased Unrestricted Linear = Refl
substitutionAddInterchange Linear Unrestricted Erased Unrestricted Unrestricted = Refl
substitutionAddInterchange Linear Unrestricted Linear Erased Erased = Refl
substitutionAddInterchange Linear Unrestricted Linear Erased Linear = Refl
substitutionAddInterchange Linear Unrestricted Linear Erased Unrestricted = Refl
substitutionAddInterchange Linear Unrestricted Linear Linear Erased = Refl
substitutionAddInterchange Linear Unrestricted Linear Linear Linear = Refl
substitutionAddInterchange Linear Unrestricted Linear Linear Unrestricted = Refl
substitutionAddInterchange Linear Unrestricted Linear Unrestricted Erased = Refl
substitutionAddInterchange Linear Unrestricted Linear Unrestricted Linear = Refl
substitutionAddInterchange Linear Unrestricted Linear Unrestricted Unrestricted = Refl
substitutionAddInterchange Linear Unrestricted Unrestricted Erased Erased = Refl
substitutionAddInterchange Linear Unrestricted Unrestricted Erased Linear = Refl
substitutionAddInterchange Linear Unrestricted Unrestricted Erased Unrestricted = Refl
substitutionAddInterchange Linear Unrestricted Unrestricted Linear Erased = Refl
substitutionAddInterchange Linear Unrestricted Unrestricted Linear Linear = Refl
substitutionAddInterchange Linear Unrestricted Unrestricted Linear Unrestricted = Refl
substitutionAddInterchange Linear Unrestricted Unrestricted Unrestricted Erased = Refl
substitutionAddInterchange Linear Unrestricted Unrestricted Unrestricted Linear = Refl
substitutionAddInterchange Linear Unrestricted Unrestricted Unrestricted Unrestricted = Refl
substitutionAddInterchange Unrestricted Erased Erased Erased Erased = Refl
substitutionAddInterchange Unrestricted Erased Erased Erased Linear = Refl
substitutionAddInterchange Unrestricted Erased Erased Erased Unrestricted = Refl
substitutionAddInterchange Unrestricted Erased Erased Linear Erased = Refl
substitutionAddInterchange Unrestricted Erased Erased Linear Linear = Refl
substitutionAddInterchange Unrestricted Erased Erased Linear Unrestricted = Refl
substitutionAddInterchange Unrestricted Erased Erased Unrestricted Erased = Refl
substitutionAddInterchange Unrestricted Erased Erased Unrestricted Linear = Refl
substitutionAddInterchange Unrestricted Erased Erased Unrestricted Unrestricted = Refl
substitutionAddInterchange Unrestricted Erased Linear Erased Erased = Refl
substitutionAddInterchange Unrestricted Erased Linear Erased Linear = Refl
substitutionAddInterchange Unrestricted Erased Linear Erased Unrestricted = Refl
substitutionAddInterchange Unrestricted Erased Linear Linear Erased = Refl
substitutionAddInterchange Unrestricted Erased Linear Linear Linear = Refl
substitutionAddInterchange Unrestricted Erased Linear Linear Unrestricted = Refl
substitutionAddInterchange Unrestricted Erased Linear Unrestricted Erased = Refl
substitutionAddInterchange Unrestricted Erased Linear Unrestricted Linear = Refl
substitutionAddInterchange Unrestricted Erased Linear Unrestricted Unrestricted = Refl
substitutionAddInterchange Unrestricted Erased Unrestricted Erased Erased = Refl
substitutionAddInterchange Unrestricted Erased Unrestricted Erased Linear = Refl
substitutionAddInterchange Unrestricted Erased Unrestricted Erased Unrestricted = Refl
substitutionAddInterchange Unrestricted Erased Unrestricted Linear Erased = Refl
substitutionAddInterchange Unrestricted Erased Unrestricted Linear Linear = Refl
substitutionAddInterchange Unrestricted Erased Unrestricted Linear Unrestricted = Refl
substitutionAddInterchange Unrestricted Erased Unrestricted Unrestricted Erased = Refl
substitutionAddInterchange Unrestricted Erased Unrestricted Unrestricted Linear = Refl
substitutionAddInterchange Unrestricted Erased Unrestricted Unrestricted Unrestricted = Refl
substitutionAddInterchange Unrestricted Linear Erased Erased Erased = Refl
substitutionAddInterchange Unrestricted Linear Erased Erased Linear = Refl
substitutionAddInterchange Unrestricted Linear Erased Erased Unrestricted = Refl
substitutionAddInterchange Unrestricted Linear Erased Linear Erased = Refl
substitutionAddInterchange Unrestricted Linear Erased Linear Linear = Refl
substitutionAddInterchange Unrestricted Linear Erased Linear Unrestricted = Refl
substitutionAddInterchange Unrestricted Linear Erased Unrestricted Erased = Refl
substitutionAddInterchange Unrestricted Linear Erased Unrestricted Linear = Refl
substitutionAddInterchange Unrestricted Linear Erased Unrestricted Unrestricted = Refl
substitutionAddInterchange Unrestricted Linear Linear Erased Erased = Refl
substitutionAddInterchange Unrestricted Linear Linear Erased Linear = Refl
substitutionAddInterchange Unrestricted Linear Linear Erased Unrestricted = Refl
substitutionAddInterchange Unrestricted Linear Linear Linear Erased = Refl
substitutionAddInterchange Unrestricted Linear Linear Linear Linear = Refl
substitutionAddInterchange Unrestricted Linear Linear Linear Unrestricted = Refl
substitutionAddInterchange Unrestricted Linear Linear Unrestricted Erased = Refl
substitutionAddInterchange Unrestricted Linear Linear Unrestricted Linear = Refl
substitutionAddInterchange Unrestricted Linear Linear Unrestricted Unrestricted = Refl
substitutionAddInterchange Unrestricted Linear Unrestricted Erased Erased = Refl
substitutionAddInterchange Unrestricted Linear Unrestricted Erased Linear = Refl
substitutionAddInterchange Unrestricted Linear Unrestricted Erased Unrestricted = Refl
substitutionAddInterchange Unrestricted Linear Unrestricted Linear Erased = Refl
substitutionAddInterchange Unrestricted Linear Unrestricted Linear Linear = Refl
substitutionAddInterchange Unrestricted Linear Unrestricted Linear Unrestricted = Refl
substitutionAddInterchange Unrestricted Linear Unrestricted Unrestricted Erased = Refl
substitutionAddInterchange Unrestricted Linear Unrestricted Unrestricted Linear = Refl
substitutionAddInterchange Unrestricted Linear Unrestricted Unrestricted Unrestricted = Refl
substitutionAddInterchange Unrestricted Unrestricted Erased Erased Erased = Refl
substitutionAddInterchange Unrestricted Unrestricted Erased Erased Linear = Refl
substitutionAddInterchange Unrestricted Unrestricted Erased Erased Unrestricted = Refl
substitutionAddInterchange Unrestricted Unrestricted Erased Linear Erased = Refl
substitutionAddInterchange Unrestricted Unrestricted Erased Linear Linear = Refl
substitutionAddInterchange Unrestricted Unrestricted Erased Linear Unrestricted = Refl
substitutionAddInterchange Unrestricted Unrestricted Erased Unrestricted Erased = Refl
substitutionAddInterchange Unrestricted Unrestricted Erased Unrestricted Linear = Refl
substitutionAddInterchange Unrestricted Unrestricted Erased Unrestricted Unrestricted = Refl
substitutionAddInterchange Unrestricted Unrestricted Linear Erased Erased = Refl
substitutionAddInterchange Unrestricted Unrestricted Linear Erased Linear = Refl
substitutionAddInterchange Unrestricted Unrestricted Linear Erased Unrestricted = Refl
substitutionAddInterchange Unrestricted Unrestricted Linear Linear Erased = Refl
substitutionAddInterchange Unrestricted Unrestricted Linear Linear Linear = Refl
substitutionAddInterchange Unrestricted Unrestricted Linear Linear Unrestricted = Refl
substitutionAddInterchange Unrestricted Unrestricted Linear Unrestricted Erased = Refl
substitutionAddInterchange Unrestricted Unrestricted Linear Unrestricted Linear = Refl
substitutionAddInterchange Unrestricted Unrestricted Linear Unrestricted Unrestricted = Refl
substitutionAddInterchange Unrestricted Unrestricted Unrestricted Erased Erased = Refl
substitutionAddInterchange Unrestricted Unrestricted Unrestricted Erased Linear = Refl
substitutionAddInterchange Unrestricted Unrestricted Unrestricted Erased Unrestricted = Refl
substitutionAddInterchange Unrestricted Unrestricted Unrestricted Linear Erased = Refl
substitutionAddInterchange Unrestricted Unrestricted Unrestricted Linear Linear = Refl
substitutionAddInterchange Unrestricted Unrestricted Unrestricted Linear Unrestricted = Refl
substitutionAddInterchange Unrestricted Unrestricted Unrestricted Unrestricted Erased = Refl
substitutionAddInterchange Unrestricted Unrestricted Unrestricted Unrestricted Linear = Refl
substitutionAddInterchange Unrestricted Unrestricted Unrestricted Unrestricted Unrestricted = Refl

||| Scaling a substituted demand commutes with charging the scaled coefficient.
public export
substitutionScaleInterchange : (q, a, b, w : Quantity) ->
  multiply q (add a (multiply b w)) =
  add (multiply q a) (multiply (multiply q b) w)
substitutionScaleInterchange Erased Erased Erased Erased = Refl
substitutionScaleInterchange Erased Erased Erased Linear = Refl
substitutionScaleInterchange Erased Erased Erased Unrestricted = Refl
substitutionScaleInterchange Erased Erased Linear Erased = Refl
substitutionScaleInterchange Erased Erased Linear Linear = Refl
substitutionScaleInterchange Erased Erased Linear Unrestricted = Refl
substitutionScaleInterchange Erased Erased Unrestricted Erased = Refl
substitutionScaleInterchange Erased Erased Unrestricted Linear = Refl
substitutionScaleInterchange Erased Erased Unrestricted Unrestricted = Refl
substitutionScaleInterchange Erased Linear Erased Erased = Refl
substitutionScaleInterchange Erased Linear Erased Linear = Refl
substitutionScaleInterchange Erased Linear Erased Unrestricted = Refl
substitutionScaleInterchange Erased Linear Linear Erased = Refl
substitutionScaleInterchange Erased Linear Linear Linear = Refl
substitutionScaleInterchange Erased Linear Linear Unrestricted = Refl
substitutionScaleInterchange Erased Linear Unrestricted Erased = Refl
substitutionScaleInterchange Erased Linear Unrestricted Linear = Refl
substitutionScaleInterchange Erased Linear Unrestricted Unrestricted = Refl
substitutionScaleInterchange Erased Unrestricted Erased Erased = Refl
substitutionScaleInterchange Erased Unrestricted Erased Linear = Refl
substitutionScaleInterchange Erased Unrestricted Erased Unrestricted = Refl
substitutionScaleInterchange Erased Unrestricted Linear Erased = Refl
substitutionScaleInterchange Erased Unrestricted Linear Linear = Refl
substitutionScaleInterchange Erased Unrestricted Linear Unrestricted = Refl
substitutionScaleInterchange Erased Unrestricted Unrestricted Erased = Refl
substitutionScaleInterchange Erased Unrestricted Unrestricted Linear = Refl
substitutionScaleInterchange Erased Unrestricted Unrestricted Unrestricted = Refl
substitutionScaleInterchange Linear Erased Erased Erased = Refl
substitutionScaleInterchange Linear Erased Erased Linear = Refl
substitutionScaleInterchange Linear Erased Erased Unrestricted = Refl
substitutionScaleInterchange Linear Erased Linear Erased = Refl
substitutionScaleInterchange Linear Erased Linear Linear = Refl
substitutionScaleInterchange Linear Erased Linear Unrestricted = Refl
substitutionScaleInterchange Linear Erased Unrestricted Erased = Refl
substitutionScaleInterchange Linear Erased Unrestricted Linear = Refl
substitutionScaleInterchange Linear Erased Unrestricted Unrestricted = Refl
substitutionScaleInterchange Linear Linear Erased Erased = Refl
substitutionScaleInterchange Linear Linear Erased Linear = Refl
substitutionScaleInterchange Linear Linear Erased Unrestricted = Refl
substitutionScaleInterchange Linear Linear Linear Erased = Refl
substitutionScaleInterchange Linear Linear Linear Linear = Refl
substitutionScaleInterchange Linear Linear Linear Unrestricted = Refl
substitutionScaleInterchange Linear Linear Unrestricted Erased = Refl
substitutionScaleInterchange Linear Linear Unrestricted Linear = Refl
substitutionScaleInterchange Linear Linear Unrestricted Unrestricted = Refl
substitutionScaleInterchange Linear Unrestricted Erased Erased = Refl
substitutionScaleInterchange Linear Unrestricted Erased Linear = Refl
substitutionScaleInterchange Linear Unrestricted Erased Unrestricted = Refl
substitutionScaleInterchange Linear Unrestricted Linear Erased = Refl
substitutionScaleInterchange Linear Unrestricted Linear Linear = Refl
substitutionScaleInterchange Linear Unrestricted Linear Unrestricted = Refl
substitutionScaleInterchange Linear Unrestricted Unrestricted Erased = Refl
substitutionScaleInterchange Linear Unrestricted Unrestricted Linear = Refl
substitutionScaleInterchange Linear Unrestricted Unrestricted Unrestricted = Refl
substitutionScaleInterchange Unrestricted Erased Erased Erased = Refl
substitutionScaleInterchange Unrestricted Erased Erased Linear = Refl
substitutionScaleInterchange Unrestricted Erased Erased Unrestricted = Refl
substitutionScaleInterchange Unrestricted Erased Linear Erased = Refl
substitutionScaleInterchange Unrestricted Erased Linear Linear = Refl
substitutionScaleInterchange Unrestricted Erased Linear Unrestricted = Refl
substitutionScaleInterchange Unrestricted Erased Unrestricted Erased = Refl
substitutionScaleInterchange Unrestricted Erased Unrestricted Linear = Refl
substitutionScaleInterchange Unrestricted Erased Unrestricted Unrestricted = Refl
substitutionScaleInterchange Unrestricted Linear Erased Erased = Refl
substitutionScaleInterchange Unrestricted Linear Erased Linear = Refl
substitutionScaleInterchange Unrestricted Linear Erased Unrestricted = Refl
substitutionScaleInterchange Unrestricted Linear Linear Erased = Refl
substitutionScaleInterchange Unrestricted Linear Linear Linear = Refl
substitutionScaleInterchange Unrestricted Linear Linear Unrestricted = Refl
substitutionScaleInterchange Unrestricted Linear Unrestricted Erased = Refl
substitutionScaleInterchange Unrestricted Linear Unrestricted Linear = Refl
substitutionScaleInterchange Unrestricted Linear Unrestricted Unrestricted = Refl
substitutionScaleInterchange Unrestricted Unrestricted Erased Erased = Refl
substitutionScaleInterchange Unrestricted Unrestricted Erased Linear = Refl
substitutionScaleInterchange Unrestricted Unrestricted Erased Unrestricted = Refl
substitutionScaleInterchange Unrestricted Unrestricted Linear Erased = Refl
substitutionScaleInterchange Unrestricted Unrestricted Linear Linear = Refl
substitutionScaleInterchange Unrestricted Unrestricted Linear Unrestricted = Refl
substitutionScaleInterchange Unrestricted Unrestricted Unrestricted Erased = Refl
substitutionScaleInterchange Unrestricted Unrestricted Unrestricted Linear = Refl
substitutionScaleInterchange Unrestricted Unrestricted Unrestricted Unrestricted = Refl

||| Each branch's bound is below the bound formed from joined source demands.
||| This is an inequality, not the false exact graded substitution formula.
public export
substitutionJoinBound : (a, b, c, d, w : Quantity) ->
  DemandLeq (joinQuantity (add a (multiply b w)) (add c (multiply d w)))
            (add (joinQuantity a c) (multiply (joinQuantity b d) w))
substitutionJoinBound a b c d w =
  rewrite joinAllows (add (joinQuantity a c) (multiply (joinQuantity b d) w))
    (add a (multiply b w)) (add c (multiply d w)) in
  rewrite addMonotone a (joinQuantity a c) (multiply b w) (multiply (joinQuantity b d) w)
    (joinUpperLeft a c) (multiplyMonotone b (joinQuantity b d) w w (joinUpperLeft b d) (demandRefl w)) in
  addMonotone c (joinQuantity a c) (multiply d w) (multiply (joinQuantity b d) w)
    (joinUpperRight a c) (multiplyMonotone d (joinQuantity b d) w w (joinUpperRight b d) (demandRefl w))

||| Pointwise sequential interchange for a shared replacement demand.
public export
substitutionCombineUsage : (a, c, w : Usage n) -> (b, d : Quantity) ->
  combineUsage (combineUsage a (scaleUsage b w)) (combineUsage c (scaleUsage d w)) =
  combineUsage (combineUsage a c) (scaleUsage (add b d) w)
substitutionCombineUsage [] [] [] b d = Refl
substitutionCombineUsage (a :: as) (c :: cs) (w :: ws) b d =
  rewrite substitutionAddInterchange a b c d w in
  cong (add (add a c) (multiply (add b d) w) ::) (substitutionCombineUsage as cs ws b d)

||| Pointwise application scaling interchange.
public export
substitutionScaleUsage : (q, b : Quantity) -> (a, w : Usage n) ->
  scaleUsage q (combineUsage a (scaleUsage b w)) =
  combineUsage (scaleUsage q a) (scaleUsage (multiply q b) w)
substitutionScaleUsage q b [] [] = Refl
substitutionScaleUsage q b (a :: as) (w :: ws) =
  rewrite substitutionScaleInterchange q a b w in
  cong (add (multiply q a) (multiply (multiply q b) w) ::) (substitutionScaleUsage q b as ws)

||| Pointwise branch bound used by the conditional substitution case.
public export
substitutionJoinUsageBound : (a, c, w : Usage n) -> (b, d : Quantity) ->
  Admits (combineUsage (joinUsage a c) (scaleUsage (joinQuantity b d) w))
         (joinUsage (combineUsage a (scaleUsage b w)) (combineUsage c (scaleUsage d w)))
substitutionJoinUsageBound [] [] [] b d = AdmitNil
substitutionJoinUsageBound (a :: as) (c :: cs) (w :: ws) b d =
  AdmitCons (substitutionJoinBound a b c d w) (substitutionJoinUsageBound as cs ws b d)

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

||| Each branch's demand lies below its pointwise alternative join.
public export
joinUsageUpperLeft : (left, right : Usage n) -> Admits (joinUsage left right) left
joinUsageUpperLeft [] [] = AdmitNil
joinUsageUpperLeft (x :: xs) (y :: ys) =
  AdmitCons (joinUpperLeft x y) (joinUsageUpperLeft xs ys)

public export
joinUsageUpperRight : (left, right : Usage n) -> Admits (joinUsage left right) right
joinUsageUpperRight [] [] = AdmitNil
joinUsageUpperRight (x :: xs) (y :: ys) =
  AdmitCons (joinUpperRight x y) (joinUsageUpperRight xs ys)
