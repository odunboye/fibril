module Workloads

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.NormalForm
import Fibril.Foundation.DeMorgan.Face

%default total

||| Fixed workload identifiers; all expect a successful observable check.
public export
data Workload = Substitution | Reduction | ErasedChecking | RuntimeChecking | IntervalEquality | FaceEntailment | FullExposure | HeadExposure

public export
parseWorkload : String -> Maybe Workload
parseWorkload "substitution" = Just Substitution
parseWorkload "reduction" = Just Reduction
parseWorkload "erased" = Just ErasedChecking
parseWorkload "runtime" = Just RuntimeChecking
parseWorkload "interval" = Just IntervalEquality
parseWorkload "face" = Just FaceEntailment
parseWorkload "expose-full" = Just FullExposure
parseWorkload "expose-head" = Just HeadExposure
parseWorkload _ = Nothing

spine : Nat -> Term n -> Term n -> Term n
spine Z function base = base
spine (S size) function base = Apply function (spine size function base)

identity : Nat -> Term 0
identity level = Lambda Erased (Universe level) (Lambda Linear (Variable FZ) (Variable FZ))

identityType : Nat -> Term 0
identityType level = Pi Erased (Universe level) (Pi Linear (Variable FZ) (Variable (FS FZ)))

wrap : Nat -> Term 0 -> Term 0 -> Term 0
wrap Z ty term = term
wrap (S size) ty term =
  Apply (Lambda Linear ty (Variable FZ)) (wrap size ty term)

intervalProduct : Nat -> Nat -> Interval Nat
intervalProduct Z offset = One
intervalProduct (S size) offset =
  Meet (Join (Var offset) (Var (S offset))) (intervalProduct size (2 + offset))

faceProduct : Nat -> Nat -> Face
faceProduct Z offset = Top
faceProduct (S size) offset =
  Conjunction (Disjunction (Endpoint offset False) (Endpoint (S offset) False))
              (faceProduct size (2 + offset))

||| Execute construction plus operation plus result validation.
||| The changing seed prevents all iterations sharing exactly one input value.
||| Size is capped by the driver; DNF products are deliberately adversarial.
public export
runWorkload : Workload -> (size : Nat) -> (seed : Nat) -> Bool
runWorkload Substitution size seed =
  sameSyntax
    (substituteTerm (\i => the (Term 0) (Universe seed))
      (spine size (the (Term 1) (Variable FZ)) (Universe seed)))
    (spine size (Universe seed) (Universe seed))
runWorkload Reduction size seed =
  case normalize size (wrap size (Universe (S seed)) (Universe seed)) of
    Normal result => sameSyntax result (Universe seed)
    OutOfFuel _ => False
runWorkload ErasedChecking size seed =
  case checkErased (100 + 8 * size) (100 + 8 * size) Empty
         (wrap size (Universe (S seed)) (Universe seed)) (Universe (S seed)) of
    Right () => True
    Left _ => False
runWorkload RuntimeChecking size seed =
  case checkRuntime (100 + 8 * size) (100 + 8 * size) Empty
         (wrap size (identityType seed) (identity seed)) (identityType seed) of
    Right _ => True
    Left _ => False
runWorkload IntervalEquality size seed =
  let term = intervalProduct size seed
   in equivalent term (Reverse (Reverse term))
runWorkload FullExposure size seed =
  case normalize size (Pi Linear (Universe 0)
         (weaken (wrap size (Universe (S seed)) (Universe seed)))) of
    Normal (Pi _ _ _) => True
    _ => False
runWorkload HeadExposure size seed =
  case weakHead 0 (Pi Linear (Universe 0)
         (weaken (wrap size (Universe (S seed)) (Universe seed)))) of
    HeadForm (Pi _ _ _) => True
    _ => False
runWorkload FaceEntailment size seed =
  entails (faceProduct size seed) (Disjunction (Endpoint seed False) (Endpoint (S seed) False))
