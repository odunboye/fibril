-- Ordinary typing of a hypothetical self reference, not recursive admission.
module Fibril.Termination.CoreCandidate

import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Quantity
import Fibril.Core.Runtime
import Fibril.Core.Term

%default total

||| A single actual core body with only self free. The body is not executable
||| recursion: the self variable is hypothetical and has no defining value.
public export
record Candidate where
  constructor MkCandidate
  signature : Term 0
  body : Term 1

||| Syntax and budget failures are separate from ordinary checker failures.
||| None of these results decides termination or admits a core definition.
public export
data HypothesisProblem = Unsupported String | AdmissionExhausted String | OrdinaryFailure RuntimeError

-- Shared node and key-character fuel count signature and body, including
-- annotations. Measuring a string itself is not a hard runtime/memory bound.
-- Unsupported constructors fail closed before ordinary type checking.
admit : (Nat, Nat) -> Term n -> Either HypothesisProblem (Nat, Nat)
admit (Z, _) _ = Left (AdmissionExhausted "core candidate node admission exhausted (256)")
admit (S nodes, payload) (Variable _) = Right (nodes, payload)
admit (S nodes, payload) (Universe _) = Right (nodes, payload)
admit (S nodes, payload) NatType = Right (nodes, payload)
admit (S nodes, payload) NatZero = Right (nodes, payload)
admit (S nodes, payload) (NatSucc value) = admit (nodes, payload) value
admit (S nodes, payload) BoolType = Right (nodes, payload)
admit (S nodes, payload) BoolTrue = Right (nodes, payload)
admit (S nodes, payload) BoolFalse = Right (nodes, payload)
admit (S nodes, payload) (BoolCase condition yes no) = do
  fuel <- admit (nodes, payload) condition
  fuel <- admit fuel yes
  admit fuel no
admit (S nodes, payload) (SeqType key element) =
  let size = length key in
    if size <= payload then admit (nodes, minus payload size) element
    else Left (AdmissionExhausted "core candidate key-payload admission exhausted (4096)")
admit (S nodes, payload) (SeqNil ty) = admit (nodes, payload) ty
admit (S nodes, payload) (SeqCons ty head tail) = do
  fuel <- admit (nodes, payload) ty
  fuel <- admit fuel head
  admit fuel tail
admit (S nodes, payload) (SeqCase motive value nil cons) = do
  fuel <- admit (nodes, payload) motive
  fuel <- admit fuel value
  fuel <- admit fuel nil
  admit fuel cons
admit (S nodes, payload) (Pi _ domain codomain) = do
  fuel <- admit (nodes, payload) domain
  admit fuel codomain
admit (S nodes, payload) (Lambda _ domain body) = do
  fuel <- admit (nodes, payload) domain
  admit fuel body
admit (S nodes, payload) (Apply function argument) = do
  fuel <- admit (nodes, payload) function
  admit fuel argument
admit (S nodes, payload) _ = Left (Unsupported "unsupported core candidate syntax")

-- Signature domains and result are literal, nondependent first-order types.
atom : Term n -> Bool
atom NatType = True
atom BoolType = True
atom (SeqType _ NatType) = True
atom _ = False

resultShape : Term n -> Bool
resultShape (Pi _ domain codomain) = atom domain && resultShape codomain
resultShape result = atom result

functionShape : Term n -> Bool
functionShape (Pi _ domain codomain) = atom domain && resultShape codomain
functionShape _ = False

||| Check a real scoped core body under an unrestricted, hypothetical self.
||| A successful result means only that the existing ordinary checker accepted
||| the type and usage under that assumption. It does not check calls, graph
||| completeness, termination, evaluation, or source/core admission. In
||| particular, a directly looping self-call can pass this function.
public export
checkHypothesis : (depth : Nat) -> (reduction : Nat) -> Candidate -> Either HypothesisProblem ()
checkHypothesis depth reduction (MkCandidate signature body) = do
  remaining <- admit (256, 4096) signature
  _ <- admit remaining body
  if functionShape signature then Right () else Left (Unsupported "expected a literal nondependent first-order function signature")
  case body of
    Lambda _ _ _ => Right ()
    _ => Left (Unsupported "expected a lambda body")
  case checkRuntime depth reduction (Extend Empty Unrestricted signature) body (weaken signature) of
    Left error => Left (OrdinaryFailure error)
    Right _ => Right ()
