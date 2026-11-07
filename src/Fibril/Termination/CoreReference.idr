-- Isolated fuelled experiment over actual restricted core bodies.
-- Not recursive core semantics, source evaluation, or backend execution.
module Fibril.Termination.CoreReference

import Data.Fin
import Fibril.Core.Context
import Fibril.Core.Reduction
import Fibril.Core.Runtime
import Fibril.Core.Size
import Fibril.Core.Term
import Fibril.Termination.CoreCandidate
import Fibril.Termination.CoreCheck
import Fibril.Termination.SizeChange

%default total

public export
data ReferenceProblem = VerificationFailure CoreCheckProblem
                      | CertificateRejected String
                      | CertificateInconclusive String
                      | InvalidInput String
                      | ReferenceAdmission String
                      | ReferenceFuelExhausted
                      | ReferenceStuck
                      | ResultCheckFailure RuntimeError

-- Canonical closed inputs only. Share both node and key-character admission
-- across the two inputs. String measurement is not a hard resource guarantee.
mutual
  inputNat : (Nat, Nat) -> Term 0 -> Either ReferenceProblem (Nat, Nat)
  inputNat (Z, _) _ = Left (ReferenceAdmission "input-node admission exhausted (128)")
  inputNat (S nodes, payload) NatZero = Right (nodes, payload)
  inputNat (S nodes, payload) (NatSucc value) = inputNat (nodes, payload) value
  inputNat _ _ = Left (InvalidInput "expected a canonical Nat")

  inputList : String -> (Nat, Nat) -> Term 0 -> Either ReferenceProblem (Nat, Nat)
  inputList key (Z, _) _ = Left (ReferenceAdmission "input-node admission exhausted (128)")
  inputList key (S nodes, payload) (SeqNil ty) = inputType key (nodes, payload) ty
  inputList key (S nodes, payload) (SeqCons ty head tail) = do
    fuel <- inputType key (nodes, payload) ty
    fuel <- inputNat fuel head
    inputList key fuel tail
  inputList _ _ _ = Left (InvalidInput "expected a canonical Nat list")

  inputType : String -> (Nat, Nat) -> Term 0 -> Either ReferenceProblem (Nat, Nat)
  inputType _ (Z, _) _ = Left (ReferenceAdmission "input-node admission exhausted (128)")
  inputType key (S nodes, payload) (SeqType actual NatType) =
    let size = length actual in
      if size > payload then Left (ReferenceAdmission "input-key admission exhausted (4096)") else
      if actual /= key then Left (InvalidInput "list key does not match the candidate") else
      case nodes of
        Z => Left (ReferenceAdmission "input-node admission exhausted (128)")
        S rest => Right (rest, minus payload size)
  inputType _ _ _ = Left (InvalidInput "expected the exact literal Nat-list type")

-- Closing succeeds only for an actual canonical list containing no self or
-- other free variable. It does not treat a stuck neutral as a result.
closeNat : Term 1 -> Maybe (Term 0)
closeNat NatZero = Just NatZero
closeNat (NatSucc value) = NatSucc <$> closeNat value
closeNat _ = Nothing

closeList : String -> Term 1 -> Maybe (Term 0)
closeList key (SeqNil (SeqType actual NatType)) =
  if actual == key then Just (SeqNil (SeqType key NatType)) else Nothing
closeList key (SeqCons (SeqType actual NatType) head tail) =
  if actual /= key then Nothing else do
    h <- closeNat head
    t <- closeList key tail
    Just (SeqCons (SeqType key NatType) h t)
closeList _ _ = Nothing

-- Current states originate only from admitted bodies and canonical inputs.
-- A single ordinary step can substitute at most the whole current term into
-- each occurrence in that term. This deliberately loose quadratic admission
-- covers the restricted transitions before constructing their result. The
-- key estimate counts every resulting node as if it carried a full key.
-- Neither estimate is a proof of time, allocation, stack, or preservation.
preflight : Nat -> Term 1 -> Term 1 -> Either ReferenceProblem ()
preflight keyLength body current =
  let nodes = coreNodes current
      bodyNodes = coreNodes body in
  if nodes > 8192 || bodyNodes > 256 then Left (ReferenceAdmission "reference state exceeds node admission") else
  let bound = (nodes + 1) * (nodes + 1) + bodyNodes + 4 in
  if bound > 8192 || bound * (keyLength + 1) > 524288
    then Left (ReferenceAdmission "reference transition growth admission exhausted")
    else Right ()

-- For the admitted grammar, recursive calls appear only as whole branch
-- expressions. An unexpected neutral is stuck, not a completed computation.
-- Both ordinary contractions and root self unfolding consume one fuel unit.
run : Nat -> String -> Term 1 -> Term 1 -> Either ReferenceProblem (Term 0)
run fuel key body current = case closeList key current of
  Just result => Right result
  Nothing => case fuel of
    Z => Left ReferenceFuelExhausted
    S rest => do
      preflight (length key) body current
      let next = case current of
            Apply (Apply (Variable FZ) first) second => Just (Apply (Apply body first) second)
            _ => step current
      case next of
        Nothing => Left ReferenceStuck
        Just pending => run rest key body pending

||| Bounded, isolated experimentation only. Rechecks exact bodies, calls and
||| closure on every invocation; it adds no recursive core/source semantics.
||| Ordinary reduction and this transition strategy are not proved to preserve
||| types or quantities. Fuel and admissions are not hard resource bounds.
public export
evaluate : (depth : Nat) -> (reduction : Nat) -> (fuel : Nat) ->
           Candidate -> List Call -> List Call -> Term 0 -> Term 0 ->
           Either ReferenceProblem (Term 0)
evaluate depth reduction fuel candidate calls certificate first second = do
  case verifyCore depth reduction candidate calls certificate of
    Left err => Left (VerificationFailure err)
    Right GraphAccepted => Right ()
    Right (GraphRejected reason) => Left (CertificateRejected reason)
    Right (GraphInconclusive reason) => Left (CertificateInconclusive reason)
  if fuel <= 4096 then Right () else Left (ReferenceAdmission "reference fuel admission exhausted (4096)")
  key <- case candidate.signature of
    Pi _ (SeqType key NatType) _ => Right key
    _ => Left (InvalidInput "candidate does not have a Nat-list argument")
  if length key <= 64 then Right () else Left (ReferenceAdmission "reference list key exceeds 64 characters")
  remaining <- inputList key (128, 4096) first
  _ <- inputList key remaining second
  result <- run fuel key candidate.body (Apply (Apply candidate.body (weaken first)) (weaken second))
  case checkRuntime depth reduction Empty result (SeqType key NatType) of
    Left err => Left (ResultCheckFailure err)
    Right _ => Right result
