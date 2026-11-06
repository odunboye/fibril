-- Separate provenance rewalk of a restricted actual Fibril core body.
-- This experiment does not admit or execute recursive definitions.
module Fibril.Termination.CoreCheck

import Data.Fin
import Data.Maybe
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Termination.CoreCandidate
import Fibril.Termination.SizeChange

%default total

public export
data CoreCheckProblem = CandidateProblem HypothesisProblem
                      | BodyOrGraphMismatch String
                      | ProposedCallsExhausted

-- Checker provenance is root/descendant identity, not producer relation rows.
data Origin = First | Second | TailFirst | TailSecond | UnrelatedHead

relation : Origin -> Nat -> Relation
relation First 0 = NonIncreasing
relation Second 1 = NonIncreasing
relation TailFirst 0 = Decreases
relation TailSecond 1 = Decreases
relation _ _ = Unknown

originAt : Nat -> List Origin -> Maybe Origin
originAt _ [] = Nothing
originAt Z (x :: _) = Just x
originAt (S k) (_ :: rest) = originAt k rest

listType : String -> Term n -> Bool
listType key (SeqType actual NatType) = actual == key
listType _ _ = False

-- A value is call-free only if every node belongs to this closed grammar;
-- a variable beyond the recorded locals is the hypothetical self, not a value.
value : String -> List Origin -> Term n -> Bool
value key env (Variable i) = isJust (originAt (finToNat i) env)
value key env NatZero = True
value key env (NatSucc x) = value key env x
value key env (SeqNil ty) = listType key ty
value key env (SeqCons ty head tail) = listType key ty && value key env head && value key env tail
value _ _ _ = False

matchesRow : String -> List Origin -> Term n -> List Relation -> Bool
matchesRow key env (Variable i) [first, second] = case originAt (finToNat i) env of
  Just origin => first == relation origin 0 && second == relation origin 1
  Nothing => False
matchesRow key env argument [Unknown, Unknown] = value key env argument
matchesRow _ _ _ _ = False

checkBranch : String -> List Origin -> Term n -> List Call -> Either CoreCheckProblem (List Call)
checkBranch key env (Apply (Apply (Variable self) first) second) edges =
  if finToNat self /= length env then Left (BodyOrGraphMismatch "call target is not self") else
    case edges of
      (Edge 0 0 [firstRow, secondRow] :: rest) =>
        if matchesRow key env first firstRow && matchesRow key env second secondRow
          then Right rest else Left (BodyOrGraphMismatch "call relation does not match the body")
      _ => Left (BodyOrGraphMismatch "missing, malformed or mismatched call site")
checkBranch key env body edges =
  if value key env body then Right edges else Left (BodyOrGraphMismatch "unsupported branch or escaped self")

checkMotive : String -> Term n -> Bool
checkMotive key (Lambda Erased domain codomain) = listType key domain && listType key codomain
checkMotive _ _ = False

checkShape : Term 0 -> Term 1 -> List Call -> Either CoreCheckProblem (List Call)
checkShape (Pi Linear (SeqType key NatType) (Pi Linear second result))
  (Lambda Linear firstDomain (Lambda Linear secondDomain
    (SeqCase motive (Variable scrutinee) nil (Lambda Linear NatType (Lambda Linear tailType cons))))) edges = do
  if listType key second && listType key result && listType key firstDomain &&
     listType key secondDomain && listType key tailType && checkMotive key motive
    then Right () else Left (BodyOrGraphMismatch "unsupported list types or motive")
  tail <- case finToNat scrutinee of
    0 => Right TailSecond
    1 => Right TailFirst
    _ => Left (BodyOrGraphMismatch "scrutinee is not an original argument")
  rest <- checkBranch key [Second, First] nil edges
  checkBranch key [tail, UnrelatedHead, Second, First] cons rest
checkShape _ _ _ = Left (BodyOrGraphMismatch "unsupported core candidate shape")

-- The restricted body has at most one call in each of two branches.
withinTwo : List a -> Bool
withinTwo [] = True
withinTwo [_] = True
withinTwo [_, _] = True
withinTwo _ = False

||| Separately rewalk exact core syntax and compare ordered call sites and cells.
||| Success concerns only this restricted body/graph experiment; it is not a
||| termination proof or authority to execute or admit a recursive program.
public export
check : (depth : Nat) -> (reduction : Nat) -> Candidate -> List Call -> Either CoreCheckProblem ()
check depth reduction candidate proposed = do
  if withinTwo proposed then Right () else Left ProposedCallsExhausted
  case checkHypothesis depth reduction candidate of
    Left err => Left (CandidateProblem err)
    Right () => Right ()
  remaining <- checkShape candidate.signature candidate.body proposed
  case remaining of
    [] => Right ()
    _ => Left (BodyOrGraphMismatch "extra call site")

||| Verify a closure only after separately checking the exact core call sites.
||| Even GraphAccepted cannot admit recursion: this fragment has no recursive
||| core semantics or proof of extraction/typing preservation.
public export
verifyCore : (depth : Nat) -> (reduction : Nat) -> Candidate -> List Call -> List Call -> Either CoreCheckProblem Verdict
verifyCore depth reduction candidate proposed certificate = do
  check depth reduction candidate proposed
  Right (verify [2] proposed certificate)
