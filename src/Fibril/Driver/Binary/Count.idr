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
decode : Nat -> Nat -> Term n -> Either CountError Nat
decode Z count term = Left CountReductionLimit
decode (S work) count NatZero = Right count
decode (S work) count (NatSucc tail) = decode work (S count) tail
decode (S work) count term = case runCountWork (stepHeadWith term) work of
  Nothing => Left CountReductionLimit
  Just (_, Nothing) => Left CountExpectedNat
  Just (remaining, Just next) => decode remaining count next

||| Bounds count-related canonical successor reads and unary construction, not
||| arbitrary existing byte allocation, substitution, CPU time or total heap.
public export
covering
decodeBinaryCount : Nat -> Term n -> Either CountError Nat
decodeBinaryCount work term = decode work 0 term
