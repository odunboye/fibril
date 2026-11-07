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
