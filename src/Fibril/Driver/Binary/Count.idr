-- Typed compact count syntax is checked by the caller before this traversal.
module Fibril.Driver.Binary.Count

import Fibril.Core.Term
import Fibril.Core.WeakHead
import Fibril.Core.Reduction.Work

%default total

public export
data CountError = CountReductionLimit | CountExpectedNat

-- Each outer visit/contraction spends one unit. Primitive operand traversal and
-- materialization spend from the SAME remainder via the CountWork policy.
-- The policy's remaining amount never increases; no per-successor fuel refresh.
covering
decodeGlobals : (Nat -> Maybe (Term 0)) -> Nat -> Nat -> Term n -> Either CountError Nat
decodeGlobals globals Z count term = Left CountReductionLimit
decodeGlobals globals (S work) count NatZero = Right count
decodeGlobals globals (S work) count (NatSucc tail) = decodeGlobals globals work (S count) tail
decodeGlobals globals (S work) count term = case runCountWork (stepHeadWithGlobals globals term) work of
  Nothing => Left CountReductionLimit
  Just (_, Nothing) => Left CountExpectedNat
  Just (remaining, Just next) => decodeGlobals globals remaining count next

||| Bounds count-related canonical successor reads and unary construction, not
||| arbitrary existing byte allocation, substitution, CPU time or total heap.
public export
covering
decodeBinaryCount : Nat -> Term n -> Either CountError Nat
decodeBinaryCount work term = decodeGlobals (const Nothing) work 0 term

public export
covering
decodeBinaryCountGlobals : (Nat -> Maybe (Term 0)) -> Nat -> Term n -> Either CountError Nat
decodeBinaryCountGlobals globals work term = decodeGlobals globals work 0 term
