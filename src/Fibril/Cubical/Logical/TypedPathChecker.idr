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

-- Restricted, proof-producing equality for neutral path applications at A.
-- No face or interval normalization is inferred beyond the declarative rules.
equalAdmitted : {n : Nat} -> (ctx : PathContext m k) -> (face : ScopedFace n) ->
                (x, y : NeutralExpr m k n) ->
                Either CheckError (NeutralEqual ctx face x y NType)
equalAdmitted ctx face (NApply (NPath p) (Meet (Var i) j))
                       (NApply (NPath q) (Var h)) =
  case decEq p q of
    No _ => Left Mismatch
    Yes Refl => case decEq i h of
      No _ => Left Mismatch
      Yes Refl => case decEq (boundedFaceEntails face (scopedEndpoint j True)) True of
        No _ => Left Unsupported
        Yes witness => Right (NIntervalApplyCong (NPathVar q) (IMeetRightOne witness))
equalAdmitted ctx face (NApply (NPath p) i) (NBase x) =
  case decEq x (left (index p ctx)) of
    Yes Refl => case decEq (boundedFaceEntails face (scopedEndpoint i False)) True of
      Yes witness => Right (NEndpointLeft (NPathVar p) (NBaseVar (left (index p ctx))) witness)
      No _ => case rightEndpoint ctx face p i (left (index p ctx)) of
        Left Mismatch => Left Unsupported
        result => result
    No _ => rightEndpoint ctx face p i x
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
