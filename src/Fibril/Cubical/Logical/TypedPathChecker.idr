module Fibril.Cubical.Logical.TypedPathChecker

import Data.Fin
import Decidable.Equality

import Data.Vect
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

public export
data CheckError = Exhausted | Unsupported | Mismatch

-- Consume a shared node allowance before inspecting or comparing any syntax.
exprNodes : Nat -> NeutralExpr m k n -> Maybe Nat
exprNodes Z _ = Nothing
exprNodes (S f) (NBase _) = Just f
exprNodes (S f) (NPath _) = Just f
exprNodes (S f) NType = Just f
exprNodes (S f) (NPathType a l r) = exprNodes f a >>= \g => exprNodes g l >>= \h => exprNodes h r
exprNodes (S f) (NAbstract body) = exprNodes f body
exprNodes (S f) (NApply p i) = exprNodes f p >>= \g => intervalNodes g i

-- Every success is the actual public declarative derivation, indexed by the
-- exact inputs. The checker never manufactures equality from a Boolean.
checkAdmitted : {n : Nat} -> (ctx : PathContext m k) -> (face : ScopedFace n) ->
                (term : NeutralExpr m k n) -> (ty : NeutralExpr m k n) ->
                Either CheckError (NeutralHasType ctx face term ty)
checkAdmitted ctx face (NBase x) NType = Right (NBaseVar x)
checkAdmitted ctx face (NPath p) (NPathType NType (NBase l) (NBase r)) =
  case decEq l (left (index p ctx)) of
    No _ => Left Mismatch
    Yes Refl => case decEq r (right (index p ctx)) of
      No _ => Left Mismatch
      Yes Refl => Right (NPathVar p)
checkAdmitted ctx face (NApply (NPath p) i) NType = Right (NElim (NPathVar p) i)
checkAdmitted ctx face (NAbstract (NBase x)) (NPathType NType (NBase l) (NBase r)) =
  case decEq l x of
    No _ => Left Mismatch
    Yes Refl => case decEq r x of
      No _ => Left Mismatch
      Yes Refl => Right (NIntro NBaseForm (NBaseVar r) (NBaseVar r)
                              (NBaseVar r) (NRefl (NBaseVar r)) (NRefl (NBaseVar r)))
checkAdmitted ctx face (NAbstract (NApply (NPath p) Zero))
  (NPathType NType (NApply (NPath q) Zero) (NApply (NPath r) Zero)) =
  case decEq p q of
    No _ => Left Mismatch
    Yes Refl => case decEq q r of
      No _ => Left Mismatch
      Yes Refl => Right (NIntro NBaseForm (NElim (NPathVar r) Zero) (NElim (NPathVar r) Zero)
        (NElim (NPathVar r) Zero) (NRefl (NElim (NPathVar r) Zero)) (NRefl (NElim (NPathVar r) Zero)))
checkAdmitted ctx face (NAbstract (NApply (NPath p) One))
  (NPathType NType (NApply (NPath q) One) (NApply (NPath r) One)) =
  case decEq p q of
    No _ => Left Mismatch
    Yes Refl => case decEq q r of
      No _ => Left Mismatch
      Yes Refl => Right (NIntro NBaseForm (NElim (NPathVar r) One) (NElim (NPathVar r) One)
        (NElim (NPathVar r) One) (NRefl (NElim (NPathVar r) One)) (NRefl (NElim (NPathVar r) One)))
checkAdmitted ctx face (NAbstract (NApply (NPath p) (Var FZ)))
  (NPathType NType (NBase l) (NBase r)) =
  case decEq l (left (index p ctx)) of
    No _ => Left Mismatch
    Yes Refl => case decEq r (right (index p ctx)) of
      No _ => Left Mismatch
      Yes Refl =>
        case decEq (boundedFaceEntails (SConjunction (weakenFace face) (SEndpoint FZ False)) (scopedEndpoint (Var FZ) False)) True of
          No _ => Left Unsupported
          Yes leftFace =>
            case decEq (boundedFaceEntails (SConjunction (weakenFace face) (SEndpoint FZ True)) (scopedEndpoint (Var FZ) True)) True of
              No _ => Left Unsupported
              Yes rightFace => Right (NIntro NBaseForm (NBaseVar (left (index p ctx)))
                (NBaseVar (right (index p ctx))) (NElim (NPathVar p) (Var FZ))
                (NEndpointLeft (NPathVar p) (NBaseVar (left (index p ctx))) leftFace)
                (NEndpointRight (NPathVar p) (NBaseVar (right (index p ctx))) rightFace))
-- The inner edge of a connection square, scoped over an existing dimension.
-- Both boundaries are justified on their restricted faces, not by vertices.
checkAdmitted ctx face
  (NAbstract (NApply (NPath p) (Meet (Var (FS i)) (Var FZ))))
  (NPathType NType (NBase l) (NApply (NPath q) (Var j))) =
  case decEq p q of
    No _ => Left Mismatch
    Yes Refl => case decEq i j of
      No _ => Left Mismatch
      Yes Refl => case decEq l (left (index q ctx)) of
        No _ => Left Mismatch
        Yes Refl =>
          case decEq (boundedFaceEntails (SConjunction (weakenFace face) (SEndpoint FZ False))
                       (scopedEndpoint (Meet (Var (FS j)) (Var FZ)) False)) True of
            No _ => Left Unsupported
            Yes leftFace =>
              case decEq (boundedFaceEntails (SConjunction (weakenFace face) (SEndpoint FZ True))
                           (scopedEndpoint (Var FZ) True)) True of
                No _ => Left Unsupported
                Yes rightFace => Right (NIntro NBaseForm (NBaseVar (left (index q ctx)))
                  (NElim (NPathVar q) (Var j))
                  (NElim (NPathVar q) (Meet (Var (FS j)) (Var FZ)))
                  (NEndpointLeft (NPathVar q) (NBaseVar (left (index q ctx))) leftFace)
                  (NIntervalApplyCong (NPathVar q) (IMeetRightOne rightFace)))
checkAdmitted ctx face (NBase _) _ = Left Mismatch
checkAdmitted ctx face (NApply (NPath _) _) _ = Left Mismatch
checkAdmitted ctx face _ _ = Left Unsupported

||| Admission caps dimensions, context lengths and a shared syntax node count.
||| No substitution is performed; generated proof terms have constant size.
public export
checkNeutral : {m, k, n : Nat} -> (budget : Nat) -> (ctx : PathContext m k) ->
               (face : ScopedFace n) -> (term : NeutralExpr m k n) ->
               (ty : NeutralExpr m k n) ->
               Either CheckError (NeutralHasType ctx face term ty)
checkNeutral {m} {k} {n} budget ctx face term ty =
  if m <= 12 && k <= 12 && n <= 12 then
    case faceNodes (min 128 budget) face >>= \f => exprNodes f term >>= \g => exprNodes g ty of
      Nothing => Left Exhausted
      Just _ => checkAdmitted ctx face term ty
  else Left Exhausted

||| Formation for A and paths over A with endpoints in the checking grammar.
public export
checkNeutralFormation : {m, k, n : Nat} -> (budget : Nat) -> (ctx : PathContext m k) ->
                        (face : ScopedFace n) -> (ty : NeutralExpr m k n) ->
                        Either CheckError (NeutralTypeFormed ctx face ty)
checkNeutralFormation {m} {k} {n} budget ctx face ty =
  if m <= 12 && k <= 12 && n <= 12 then
    case faceNodes (min 128 budget) face >>= \f => exprNodes f ty of
      Nothing => Left Exhausted
      Just _ => case ty of
        NType => Right NBaseForm
        NPathType NType l r => case checkAdmitted ctx face l NType of
          Left e => Left e
          Right lp => case checkAdmitted ctx face r NType of
            Left e => Left e
            Right rp => Right (NPathForm NBaseForm lp rp)
        _ => Left Unsupported
  else Left Exhausted

-- Try the right endpoint independently, including when both endpoints coincide.
rightEndpoint : {n : Nat} -> (ctx : PathContext m k) -> (face : ScopedFace n) ->
                (p : Fin k) -> (i : ScopedInterval n) -> (x : Fin m) ->
                Either CheckError (NeutralEqual ctx face (NApply (NPath p) i) (NBase x) NType)
rightEndpoint ctx face p i x =
  case decEq x (right (index p ctx)) of
    No _ => Left Mismatch
    Yes Refl => case decEq (boundedFaceEntails face (scopedEndpoint i True)) True of
      Yes witness => Right (NEndpointRight (NPathVar p) (NBaseVar (right (index p ctx))) witness)
      No _ => Left Unsupported

-- Structural comparison returns propositional equality, never a Boolean witness.
intervalSame : (x, y : ScopedInterval n) -> Maybe (x = y)
intervalSame Zero Zero = Just Refl
intervalSame One One = Just Refl
intervalSame (Var i) (Var j) = case decEq i j of
  Yes Refl => Just Refl
  No _ => Nothing
intervalSame (Meet a b) (Meet c d) = do
  Refl <- intervalSame a c
  Refl <- intervalSame b d
  Just Refl
intervalSame (Join a b) (Join c d) = do
  Refl <- intervalSame a c
  Refl <- intervalSame b d
  Just Refl
intervalSame (Reverse a) (Reverse b) = do
  Refl <- intervalSame a b
  Just Refl
intervalSame _ _ = Nothing

intervalForward : {n : Nat} -> (face : ScopedFace n) -> (x, y : ScopedInterval n) ->
                  Maybe (IntervalEquivalent face x y)
intervalForward face x y = case intervalSame x y of
  Just Refl => Just IRefl
  Nothing => meetOne x y
  where
    meetOne : (a, b : ScopedInterval n) -> Maybe (IntervalEquivalent face a b)
    meetOne (Meet l r) b = case intervalSame l b of
      Just Refl => case decEq (boundedFaceEntails face (scopedEndpoint r True)) True of
        Yes prf => Just (IMeetRightOne prf)
        No _ => tryLeft b r b
      Nothing => tryLeft l r b
      where
        tryLeft : (l, r, b : ScopedInterval n) -> Maybe (IntervalEquivalent face (Meet l r) b)
        tryLeft l r b = case intervalSame r b of
          Just Refl => case decEq (boundedFaceEntails face (scopedEndpoint l True)) True of
            Yes prf => Just (IMeetLeftOne prf)
            No _ => Nothing
          Nothing => Nothing
    meetOne _ _ = Nothing

endpointEqual : {n : Nat} -> (ctx : PathContext m k) -> (face : ScopedFace n) ->
                (p : Fin k) -> (i : ScopedInterval n) -> (x : Fin m) ->
                Either CheckError (NeutralEqual ctx face (NApply (NPath p) i) (NBase x) NType)
endpointEqual ctx face p i x =
  case decEq x (left (index p ctx)) of
    Yes Refl => case decEq (boundedFaceEntails face (scopedEndpoint i False)) True of
      Yes witness => Right (NEndpointLeft (NPathVar p) (NBaseVar (left (index p ctx))) witness)
      No _ => case rightEndpoint ctx face p i (left (index p ctx)) of
        Left Mismatch => Left Unsupported
        result => result
    No _ => rightEndpoint ctx face p i x

-- Typed base equality: reflexivity, endpoint rules, and either orientation of
-- the declarative meet-one congruences for arbitrary admitted intervals.
equalAdmitted : {n : Nat} -> (ctx : PathContext m k) -> (face : ScopedFace n) ->
                (x, y : NeutralExpr m k n) ->
                Either CheckError (NeutralEqual ctx face x y NType)
equalAdmitted ctx face (NBase x) (NBase y) = case decEq x y of
  Yes Refl => Right (NRefl (NBaseVar y))
  No _ => Left Mismatch
equalAdmitted ctx face (NApply (NPath p) i) (NApply (NPath q) j) =
  case decEq p q of
    No _ => Left Mismatch
    Yes Refl => case intervalForward face i j of
      Just eq => Right (NIntervalApplyCong (NPathVar q) eq)
      Nothing => case intervalForward face j i of
        Just eq => Right (NSym (NIntervalApplyCong (NPathVar q) eq))
        Nothing => Left Unsupported
equalAdmitted ctx face (NApply (NPath p) i) (NBase x) = endpointEqual ctx face p i x
equalAdmitted ctx face (NBase x) (NApply (NPath p) i) =
  case endpointEqual ctx face p i x of
    Left e => Left e
    Right eq => Right (NSym eq)
equalAdmitted ctx face _ _ = Left Unsupported

||| Check the restricted application equalities above with a shared input cap.
||| The generated entailment goals are linear in the already-admitted interval.
public export
checkNeutralEqual : {m, k, n : Nat} -> (budget : Nat) -> (ctx : PathContext m k) ->
                    (face : ScopedFace n) -> (x, y : NeutralExpr m k n) ->
                    Either CheckError (NeutralEqual ctx face x y NType)
checkNeutralEqual {m} {k} {n} budget ctx face x y =
  if m <= 12 && k <= 12 && n <= 12 then
    case faceNodes (min 128 budget) face >>= \f => exprNodes f x >>= \g => exprNodes g y of
      Nothing => Left Exhausted
      Just _ => equalAdmitted ctx face x y
  else Left Exhausted

typeEqualAdmitted : {n : Nat} -> (ctx : PathContext m k) -> (face : ScopedFace n) ->
                    (x, y : NeutralExpr m k n) ->
                    Either CheckError (NeutralTypeEqual ctx face x y)
typeEqualAdmitted ctx face NType NType = Right (NTypeRefl NBaseForm)
typeEqualAdmitted ctx face (NPathType NType l r) (NPathType NType l' r') = do
  lp <- checkAdmitted ctx face l NType
  rp <- checkAdmitted ctx face r NType
  lq <- checkAdmitted ctx face l' NType
  rq <- checkAdmitted ctx face r' NType
  le <- equalAdmitted ctx face l l'
  re <- equalAdmitted ctx face r r'
  Right (NPathTypeCong NBaseForm lp rp lq rq le re)
typeEqualAdmitted ctx face _ _ = Left Unsupported

||| Face-sensitive equality of base path types, with all four endpoint typings.
public export
checkNeutralTypeEqual : {m, k, n : Nat} -> (budget : Nat) -> (ctx : PathContext m k) ->
                        (face : ScopedFace n) -> (x, y : NeutralExpr m k n) ->
                        Either CheckError (NeutralTypeEqual ctx face x y)
checkNeutralTypeEqual {m} {k} {n} budget ctx face x y =
  if m <= 12 && k <= 12 && n <= 12 then
    case faceNodes (min 128 budget) face >>= \f => exprNodes f x >>= \g => exprNodes g y of
      Nothing => Left Exhausted
      Just _ => typeEqualAdmitted ctx face x y
  else Left Exhausted

-- Both abstractions are checked at the exact requested path type before their
-- bodies are compared on the weakened face.
pathEqualAdmitted : {n : Nat} -> (ctx : PathContext m k) -> (face : ScopedFace n) ->
                    (x, y : NeutralExpr m k n) -> (ty : NeutralExpr m k n) ->
                    Either CheckError (NeutralEqual ctx face x y ty)
pathEqualAdmitted ctx face (NAbstract x) (NAbstract y) (NPathType NType l r) = do
  xp <- checkAdmitted ctx face (NAbstract x) (NPathType NType l r)
  yp <- checkAdmitted ctx face (NAbstract y) (NPathType NType l r)
  bodies <- equalAdmitted ctx (weakenFace face) x y
  Right (NAbstractCong {a = NType} xp yp bodies)
pathEqualAdmitted ctx face _ _ _ = Left Unsupported

||| Equality of accepted abstractions at a base path type.
public export
checkNeutralPathEqual : {m, k, n : Nat} -> (budget : Nat) -> (ctx : PathContext m k) ->
                        (face : ScopedFace n) -> (x, y, ty : NeutralExpr m k n) ->
                        Either CheckError (NeutralEqual ctx face x y ty)
checkNeutralPathEqual {m} {k} {n} budget ctx face x y ty =
  if m <= 12 && k <= 12 && n <= 12 then
    case faceNodes (min 128 budget) face >>= \f => exprNodes f x >>= \g =>
         exprNodes g y >>= \h => exprNodes h ty of
      Nothing => Left Exhausted
      Just _ => pathEqualAdmitted ctx face x y ty
  else Left Exhausted

||| Convert an existing exact typing using the checker's face-sensitive type equality.
public export
convertNeutralTyping : {m, k, n : Nat} -> (budget : Nat) -> (ctx : PathContext m k) ->
  (face : ScopedFace n) -> (term, sourceTy, targetTy : NeutralExpr m k n) ->
  NeutralHasType ctx face term sourceTy -> Either CheckError (NeutralHasType ctx face term targetTy)
convertNeutralTyping {m} {k} {n} budget ctx face term sourceTy targetTy derivation =
  if m <= 12 && k <= 12 && n <= 12 then
    case faceNodes (min 128 budget) face >>= \f => exprNodes f term >>= \g =>
         exprNodes g sourceTy >>= \h => exprNodes h targetTy of
      Nothing => Left Exhausted
      Just _ => case typeEqualAdmitted ctx face sourceTy targetTy of
        Left e => Left e
        Right eq => Right (NConvert derivation eq)
  else Left Exhausted

||| Restrict an existing exact typing only when bounded entailment proves the inclusion.
public export
restrictNeutralTyping : {m, k, n : Nat} -> (budget : Nat) -> (ctx : PathContext m k) ->
  (source, face : ScopedFace n) -> (term, ty : NeutralExpr m k n) ->
  NeutralHasType ctx source term ty -> Either CheckError (NeutralHasType ctx face term ty)
restrictNeutralTyping {m} {k} {n} budget ctx source face term ty derivation =
  if m <= 12 && k <= 12 && n <= 12 then
    case faceNodes (min 128 budget) source >>= \f => faceNodes f face >>= \g =>
         exprNodes g term >>= \h => exprNodes h ty of
      Nothing => Left Exhausted
      Just _ => case decEq (boundedFaceEntails face source) True of
        Yes witness => Right (NFaceRestrict derivation witness)
        No _ => Left Unsupported
  else Left Exhausted

||| Convert an exact equality, requiring independently indexed target typings.
public export
convertNeutralEquality : {m, k, n : Nat} -> (budget : Nat) -> (ctx : PathContext m k) ->
  (face : ScopedFace n) -> (x, y, sourceTy, targetTy : NeutralExpr m k n) ->
  NeutralEqual ctx face x y sourceTy -> NeutralHasType ctx face x targetTy ->
  NeutralHasType ctx face y targetTy -> Either CheckError (NeutralEqual ctx face x y targetTy)
convertNeutralEquality {m} {k} {n} budget ctx face x y sourceTy targetTy derivation xp yp =
  if m <= 12 && k <= 12 && n <= 12 then
    case faceNodes (min 128 budget) face >>= \f => exprNodes f x >>= \g =>
         exprNodes g y >>= \h => exprNodes h sourceTy >>= \i => exprNodes i targetTy of
      Nothing => Left Exhausted
      Just _ => case typeEqualAdmitted ctx face sourceTy targetTy of
        Left e => Left e
        Right eq => Right (NEqualConvert derivation eq xp yp)
  else Left Exhausted

-- Count the expanded result without constructing substitutions or weakened
-- replacements. Weakening preserves interval node counts under each binder.
subIntervalNodes : Nat -> (Fin n -> Nat) -> ScopedInterval n -> Maybe Nat
subIntervalNodes f sizes (Var i) = spend f (sizes i)
  where
    spend : Nat -> Nat -> Maybe Nat
    spend f Z = Just f
    spend Z (S _) = Nothing
    spend (S f) (S n) = spend f n
subIntervalNodes Z _ _ = Nothing
subIntervalNodes (S f) sizes Zero = Just f
subIntervalNodes (S f) sizes One = Just f
subIntervalNodes (S f) sizes (Reverse x) = subIntervalNodes f sizes x
subIntervalNodes (S f) sizes (Meet x y) = subIntervalNodes f sizes x >>= \g => subIntervalNodes g sizes y
subIntervalNodes (S f) sizes (Join x y) = subIntervalNodes f sizes x >>= \g => subIntervalNodes g sizes y

subExprNodes : Nat -> (Fin n -> Nat) -> NeutralExpr m k n -> Maybe Nat
subExprNodes Z _ _ = Nothing
subExprNodes (S f) sizes (NBase _) = Just f
subExprNodes (S f) sizes (NPath _) = Just f
subExprNodes (S f) sizes NType = Just f
subExprNodes (S f) sizes (NPathType a l r) =
  subExprNodes f (liftSizes sizes) a >>= \g => subExprNodes g sizes l >>= \h => subExprNodes h sizes r
  where
    liftSizes : (Fin n -> Nat) -> Fin (S n) -> Nat
    liftSizes sizes FZ = 1
    liftSizes sizes (FS i) = sizes i
subExprNodes (S f) sizes (NAbstract body) = subExprNodes f (liftSizes sizes) body
  where
    liftSizes : (Fin n -> Nat) -> Fin (S n) -> Nat
    liftSizes sizes FZ = 1
    liftSizes sizes (FS i) = sizes i
subExprNodes (S f) sizes (NApply p i) = subExprNodes f sizes p >>= \g => subIntervalNodes g sizes i

intervalSize : ScopedInterval n -> Nat
intervalSize Zero = 1
intervalSize One = 1
intervalSize (Var _) = 1
intervalSize (Reverse x) = S (intervalSize x)
intervalSize (Meet x y) = S (intervalSize x + intervalSize y)
intervalSize (Join x y) = S (intervalSize x + intervalSize y)

||| Admit both inputs before counting the expanded output; each occurrence of
||| the replacement is charged separately, including under nested binders.
public export
boundedInstantiate : {m, k, n : Nat} -> (budget : Nat) -> (i : ScopedInterval n) ->
  (body : NeutralExpr m k (S n)) -> Either CheckError (NeutralExpr m k n)
boundedInstantiate {m} {k} {n} budget i body =
  if m <= 12 && k <= 12 && n <= 11 then
    case intervalNodes (min 128 budget) i >>= \f => exprNodes f body of
      Nothing => Left Exhausted
      Just f => case subExprNodes f (sizes (intervalSize i)) body of
        Nothing => Left Exhausted
        Just _ => Right (mapNeutralDimensions (instantiateDimension i) body)
  else Left Exhausted
  where
    sizes : Nat -> Fin (S n) -> Nat
    sizes size FZ = size
    sizes size (FS _) = 1

-- A token pays for one recursive visit or one fixed-cap operation, not one
-- machine step. Errors retain the unused tokens so fallback cannot reset them.
record Metered a where
  constructor MkMetered
  runMetered : Nat -> (Nat, Either CheckError a)

Functor Metered where
  map f (MkMetered action) = MkMetered $ \fuel =>
    case action fuel of
      (remaining, Left err) => (remaining, Left err)
      (remaining, Right value) => (remaining, Right (f value))

Applicative Metered where
  pure value = MkMetered $ \fuel => (fuel, Right value)
  (<*>) mf mx = MkMetered $ \fuel =>
    case runMetered mf fuel of
      (remaining, Left err) => (remaining, Left err)
      (remaining, Right f) => runMetered (map f mx) remaining

Monad Metered where
  (>>=) action next = MkMetered $ \fuel =>
    case runMetered action fuel of
      (remaining, Left err) => (remaining, Left err)
      (remaining, Right value) => runMetered (next value) remaining

meterError : CheckError -> Metered a
meterError err = MkMetered $ \fuel => (fuel, Left err)

-- Delay the operation until after reserving its token.
boundedWork : Lazy (Either CheckError a) -> Metered a
boundedWork action = MkMetered $ \fuel => case fuel of
  Z => (Z, Left Exhausted)
  S remaining => (remaining, action)

visit : Metered ()
visit = boundedWork (Right ())

admit : Maybe Nat -> Either CheckError ()
admit Nothing = Left Exhausted
admit (Just _) = Right ()

-- Recursive formation shares the same meter as introduction when called by it.
dependentFormation : {m, k, n : Nat} -> Nat -> (ctx : PathContext m k) ->
  (face : ScopedFace n) -> (ty : NeutralExpr m k n) ->
  Metered (NeutralTypeFormed ctx face ty)
dependentFormation Z ctx face ty = meterError Exhausted
dependentFormation (S depth) {m} {k} {n} ctx face ty = do
  _ <- visit
  case m <= 12 && k <= 12 && n <= 12 of
    True => do
      _ <- boundedWork (admit (faceNodes 128 face >>= \f => exprNodes f ty))
      form ty
    False => meterError Exhausted
  where
    form : (ty : NeutralExpr m k n) -> Metered (NeutralTypeFormed ctx face ty)
    form NType = pure NBaseForm
    form (NPathType family l r) = do
      _ <- boundedWork (boundedInstantiate 128 Zero family)
      _ <- boundedWork (boundedInstantiate 128 One family)
      fp <- dependentFormation depth ctx (weakenFace face) family
      lp <- boundedWork (checkNeutral 128 ctx face l (mapNeutralDimensions TypedPath.faceZero family))
      rp <- boundedWork (checkNeutral 128 ctx face r (mapNeutralDimensions TypedPath.faceOne family))
      pure (NPathPForm fp lp rp)
    form _ = meterError Unsupported

||| Formation of nested dependent path types with a shared work-token allowance.
public export
checkDependentFormation : {m, k, n : Nat} -> (budget : Nat) -> (ctx : PathContext m k) ->
  (face : ScopedFace n) -> (ty : NeutralExpr m k n) ->
  Either CheckError (NeutralTypeFormed ctx face ty)
checkDependentFormation budget ctx face ty =
  snd (runMetered (dependentFormation 12 ctx face ty) budget)

-- Structural equality produces an equality of the actual syntax indices.
neutralSame : (x, y : NeutralExpr m k n) -> Maybe (x = y)
neutralSame (NBase x) (NBase y) = case decEq x y of
  Yes Refl => Just Refl
  No _ => Nothing
neutralSame (NPath x) (NPath y) = case decEq x y of
  Yes Refl => Just Refl
  No _ => Nothing
neutralSame NType NType = Just Refl
neutralSame (NPathType a l r) (NPathType b l' r') = do
  Refl <- neutralSame a b
  Refl <- neutralSame l l'
  Refl <- neutralSame r r'
  Just Refl
neutralSame (NAbstract x) (NAbstract y) = do
  Refl <- neutralSame x y
  Just Refl
neutralSame (NApply p i) (NApply q j) = do
  Refl <- neutralSame p q
  Refl <- intervalSame i j
  Just Refl
neutralSame _ _ = Nothing

||| Check an application using an already established exact PathP derivation.
||| The proof tree is supplied, not synthesized or bounded by this function.
public export
checkDependentApplication : {m, k, n : Nat} -> (budget : Nat) -> (ctx : PathContext m k) ->
  (face : ScopedFace n) -> (p : NeutralExpr m k n) -> (i : ScopedInterval n) ->
  (family : NeutralExpr m k (S n)) -> (l, r, expected : NeutralExpr m k n) ->
  NeutralHasType ctx face p (NPathType family l r) ->
  Either CheckError (NeutralHasType ctx face (NApply p i) expected)
checkDependentApplication {m} {k} {n} budget ctx face p i family l r expected derivation =
  if m <= 12 && k <= 12 && n <= 11 then
    case faceNodes (min 128 budget) face >>= \a => exprNodes a p >>= \b =>
         intervalNodes b i >>= \c => exprNodes c family >>= \d =>
         exprNodes d l >>= \e => exprNodes e r >>= \f => exprNodes f expected of
      Nothing => Left Exhausted
      Just _ => do
        _ <- boundedInstantiate budget i family
        case neutralSame (mapNeutralDimensions (instantiateDimension i) family) expected of
          Nothing => Left Mismatch
          Just same => case same of
            Refl => Right (NPathPElim derivation i)
  else Left Exhausted

-- Choose an endpoint only when the restricted body proves that its declared
-- path application is at a declared endpoint. The candidate is syntax, not
-- evidence; exact introduction and type conversion check it independently.
inferBaseEndpoint : {n : Nat} -> (ctx : PathContext m k) -> (face : ScopedFace n) ->
  Bool -> NeutralExpr m k (S n) -> NeutralExpr m k n -> NeutralExpr m k n
inferBaseEndpoint ctx face side (NBase x) fallback = NBase x
inferBaseEndpoint ctx face side (NApply (NPath p) i) fallback =
  let restricted = SConjunction (weakenFace face) (SEndpoint FZ side) in
  if boundedFaceEntails restricted (scopedEndpoint i False)
    then NBase (left (index p ctx))
  else if boundedFaceEntails restricted (scopedEndpoint i True)
    then NBase (right (index p ctx))
  else fallback
inferBaseEndpoint ctx face side body fallback = fallback

-- Recursive calls and bounded subchecks draw from one meter, including retries.
mutual
  introTyping : {m, k, n : Nat} -> Nat -> (ctx : PathContext m k) ->
    (face : ScopedFace n) -> (term, ty : NeutralExpr m k n) ->
    Metered (NeutralHasType ctx face term ty)
  introTyping Z ctx face term ty = meterError Exhausted
  introTyping (S depth) {m} {k} {n} ctx face term ty = do
    _ <- visit
    case m <= 12 && k <= 12 && n <= 12 of
      True => do
        _ <- boundedWork (admit (faceNodes 128 face >>= \f => exprNodes f term >>= \g => exprNodes g ty))
        go term ty
      False => meterError Exhausted
    where
      go : (term, ty : NeutralExpr m k n) -> Metered (NeutralHasType ctx face term ty)
      go (NAbstract body) (NPathType NType l r) = MkMetered $ \fuel =>
        case runMetered (introExact depth ctx face body NType l r) fuel of
          (remaining, Right derivation) => (remaining, Right derivation)
          (remaining, Left Exhausted) => (remaining, Left Exhausted)
          (remaining, Left original) => runMetered (fallback original) remaining
        where
          fallback : CheckError -> Metered (NeutralHasType ctx face (NAbstract body) (NPathType NType l r))
          fallback original = do
            -- Candidate inference invokes only the fixed bounded face solver.
            (l', r') <- boundedWork (Right (inferBaseEndpoint ctx face False body l,
                                             inferBaseEndpoint ctx face True body r))
            _ <- boundedWork (admit (faceNodes 128 face >>= \a =>
                 exprNodes a (NAbstract body) >>= \b =>
                 exprNodes b (NPathType NType l r) >>= \c =>
                 exprNodes c (NPathType NType l' r')))
            MkMetered $ \fuel => case runMetered (boundedWork (typeEqualAdmitted ctx face
                  (NPathType NType l' r') (NPathType NType l r))) fuel of
              (remaining, Left Exhausted) => (remaining, Left Exhausted)
              (remaining, Left _) => (remaining, Left original)
              (remaining, Right conversion) =>
                case runMetered (introExact depth ctx face body NType l' r') remaining of
                  (rest, Left Exhausted) => (rest, Left Exhausted)
                  (rest, Left _) => (rest, Left original)
                  (rest, Right derivation) => (rest, Right (NConvert derivation conversion))
      go (NAbstract body) (NPathType family l r) =
        introExact depth ctx face body family l r
      go (NPath p) ty = do
        eq <- boundedWork (typeEqualAdmitted ctx face
          (NPathType NType (NBase (left (index p ctx))) (NBase (right (index p ctx)))) ty)
        pure (NConvert (NPathVar p) eq)
      go term ty = boundedWork (checkAdmitted ctx face term ty)

  introExact : {m, k, n : Nat} -> Nat -> (ctx : PathContext m k) ->
    (face : ScopedFace n) -> (body, family : NeutralExpr m k (S n)) ->
    (l, r : NeutralExpr m k n) ->
    Metered (NeutralHasType ctx face (NAbstract body) (NPathType family l r))
  introExact Z ctx face body family l r = meterError Exhausted
  introExact (S depth) ctx face body family l r = do
        _ <- visit
        _ <- boundedWork (boundedInstantiate 128 Zero family)
        _ <- boundedWork (boundedInstantiate 128 One family)
        fp <- dependentFormation depth ctx (weakenFace face) family
        lp <- introTyping depth ctx face l (mapNeutralDimensions TypedPath.faceZero family)
        rp <- introTyping depth ctx face r (mapNeutralDimensions TypedPath.faceOne family)
        bp <- introTyping depth ctx (weakenFace face) body family
        le <- introBoundary depth ctx (SConjunction (weakenFace face) (SEndpoint FZ False)) body (weakenNeutralDimensions l) family
        re <- introBoundary depth ctx (SConjunction (weakenFace face) (SEndpoint FZ True)) body (weakenNeutralDimensions r) family
        pure (NPathPIntro fp lp rp bp le re)

  introBoundary : {m, k, n : Nat} -> Nat -> (ctx : PathContext m k) ->
    (face : ScopedFace n) -> (x, y, ty : NeutralExpr m k n) ->
    Metered (NeutralEqual ctx face x y ty)
  introBoundary Z ctx face x y ty = meterError Exhausted
  introBoundary (S depth) {m} {k} {n} ctx face x y ty = do
    _ <- visit
    case m <= 12 && k <= 12 && n <= 12 of
      True => do
        _ <- boundedWork (admit (faceNodes 128 face >>= \a => exprNodes a x >>= \b =>
             exprNodes b y >>= \c => exprNodes c ty))
        go x y ty
      False => meterError Exhausted
    where
      go : (x, y, ty : NeutralExpr m k n) -> Metered (NeutralEqual ctx face x y ty)
      go x y NType = boundedWork (equalAdmitted ctx face x y)
      go (NAbstract x) (NAbstract y) (NPathType family l r) = do
        xp <- introTyping depth ctx face (NAbstract x) (NPathType family l r)
        yp <- introTyping depth ctx face (NAbstract y) (NPathType family l r)
        bodies <- introBoundary depth ctx (weakenFace face) x y family
        pure (NPathPAbstractCong xp yp bodies)
      go x y ty = do
        same <- boundedWork (Right (neutralSame x y))
        case same of
          Nothing => meterError Unsupported
          Just Refl => do
            xp <- introTyping depth ctx face y ty
            pure (NRefl xp)

||| Autonomous dependent introduction with shared work tokens and fixed depth.
public export
checkDependentIntroduction : {m, k, n : Nat} -> (budget : Nat) -> (ctx : PathContext m k) ->
  (face : ScopedFace n) -> (term, ty : NeutralExpr m k n) ->
  Either CheckError (NeutralHasType ctx face term ty)
checkDependentIntroduction budget ctx face (NAbstract body) (NPathType family l r) =
  snd (runMetered (introTyping 12 ctx face (NAbstract body) (NPathType family l r)) budget)
checkDependentIntroduction budget ctx face term ty = Left Unsupported
