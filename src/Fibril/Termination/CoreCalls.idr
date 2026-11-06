-- Experimental extraction from one restricted actual Fibril core body.
-- The output is untrusted and authorizes no evaluation or source recursion.
module Fibril.Termination.CoreCalls

import Data.Fin
import Data.List
import Data.Maybe
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Termination.CoreCandidate
import Fibril.Termination.SizeChange

%default total

public export
data ExtractionProblem = HypothesisFailure HypothesisProblem | UnsupportedCore String

sameList : String -> Term n -> Bool
sameList key (SeqType other NatType) = key == other
sameList _ _ = False

-- Only actual scoped locals, with no access to the hypothetical self.
lookupRow : Nat -> List (List Relation) -> Maybe (List Relation)
lookupRow _ [] = Nothing
lookupRow Z (row :: _) = Just row
lookupRow (S index) (_ :: rows) = lookupRow index rows

-- This value fragment has no applications or hidden recursive calls. Constructor
-- annotations are literal and checked against the candidate's exact list key.
valueOK : String -> List (List Relation) -> Term n -> Bool
valueOK key env (Variable index) = isJust (lookupRow (finToNat index) env)
valueOK key env NatZero = True
valueOK key env (NatSucc value) = valueOK key env value
valueOK key env (SeqNil ty) = sameList key ty
valueOK key env (SeqCons ty head tail) = sameList key ty && valueOK key env head && valueOK key env tail
valueOK _ _ _ = False

argRow : String -> List (List Relation) -> Term n -> Maybe (List Relation)
argRow key env (Variable index) = lookupRow (finToNat index) env
argRow key env value = if valueOK key env value then Just [Unknown, Unknown] else Nothing

-- Self is immediately outside the locals in the explicitly matched scope.
-- A branch is either one direct saturated call or a call-free value. Calls
-- nested inside values, arguments, annotations, or unknown forms are rejected.
branch : String -> List (List Relation) -> Term n -> Either ExtractionProblem (List Call)
branch key env (Apply (Apply (Variable self) first) second) =
  if finToNat self /= length env then Left (UnsupportedCore "call target is not the scoped self") else
    case (argRow key env first, argRow key env second) of
      (Just firstRow, Just secondRow) => Right [Edge 0 0 [firstRow, secondRow]]
      _ => Left (UnsupportedCore "unsupported or recursive call argument")
branch key env value =
  if valueOK key env value then Right [] else Left (UnsupportedCore "unsupported branch expression or escaped self")

-- These syntactic restrictions ensure that no case motive, binder annotation,
-- or scrutinee can conceal a call. They are stricter than ordinary core typing.
motiveOK : String -> Term n -> Bool
motiveOK key (Lambda Erased domain result) = sameList key domain && sameList key result
motiveOK _ _ = False

extractShape : Term 0 -> Term 1 -> Either ExtractionProblem (List Call)
extractShape (Pi Linear ty1 (Pi Linear ty2 result))
  (Lambda Linear domain1 (Lambda Linear domain2
    (SeqCase motive (Variable scrutinee) nil (Lambda Linear NatType (Lambda Linear tailTy cons))))) =
  case ty1 of
    SeqType key NatType =>
      if not (sameList key ty2 && sameList key result && sameList key domain1 &&
              sameList key domain2 && sameList key tailTy && motiveOK key motive)
        then Left (UnsupportedCore "list signature, annotations or motive are outside the fragment")
        else do
          root <- case finToNat scrutinee of
            0 => Right 1 -- second argument is newest
            1 => Right 0
            _ => Left (UnsupportedCore "case scrutinee is not a function parameter")
          let initial = [[Unknown, NonIncreasing], [NonIncreasing, Unknown]]
          let smaller = if root == 0 then [Decreases, Unknown] else [Unknown, Decreases]
          nilCalls <- branch key initial nil
          consCalls <- branch key (smaller :: [Unknown, Unknown] :: initial) cons
          Right (nilCalls ++ consCalls)
    _ => Left (UnsupportedCore "expected a Nat-list signature")
extractShape _ _ = Left (UnsupportedCore "expected two linear list parameters and a direct list case")

||| Extract candidate direct calls from a tightly restricted, ordinarily checked
||| open core body. This is a single producer, not an independent authenticator.
||| Its graph must not be used to authorize a recursive core or source program.
public export
extract : (depth : Nat) -> (reduction : Nat) -> Candidate -> Either ExtractionProblem (List Call)
extract depth reduction candidate = do
  case checkHypothesis depth reduction candidate of
    Left problem => Left (HypothesisFailure problem)
    Right () => Right ()
  extractShape candidate.signature candidate.body
