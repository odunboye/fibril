-- Raw core/policy evidence, distinct from checked .fib integration tests.
module Tests.BinaryCount

import Data.Fin
import Data.List
import Fibril.Data.Bytes
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Driver.Binary.Count

%default total

-- This equation cannot invoke naturalTerm 1000000: reservation denies before
-- the arbitrary builder is called. The general theorem lives in Work.idr.
unbuiltLargeNatural : runCountWork
  (reserveNatural 1000000 (the (Nat -> Term 0) Fibril.Core.Term.naturalTerm)) 4096 = Nothing
unbuiltLargeNatural = reserveNaturalDenied 1000000 4096 Fibril.Core.Term.naturalTerm Refl

bytes : Nat -> Term 0
bytes amount = BytesValue (fromList (replicate amount 97))

length : Nat -> Term 0
length amount = BytesLength (bytes amount)

rejected : Maybe a -> Bool
rejected Nothing = True
rejected _ = False

covering
succeeds : Nat -> Nat -> Term 0 -> Bool
succeeds work expected term = case decodeBinaryCount work term of
  Right actual => actual == expected
  _ => False

covering
exhausts : Nat -> Term 0 -> Bool
exhausts work term = case decodeBinaryCount work term of
  Left CountReductionLimit => True
  _ => False

foldCount : Term 0 -> Term 0
foldCount count = NatRec (Lambda Erased NatType NatType) NatZero
  (Lambda Erased NatType (Lambda Linear NatType (NatSucc (Variable FZ)))) count

indexCount : Term 0
indexCount = VariantCase (Lambda Erased byteIndexResultType NatType)
  (BytesIndex NatZero (BytesValue (fromList [255])))
  [NatZero, Lambda Linear NatType (Variable FZ)]

public export
covering
checks : List (String, Bool)
checks =
  [("count materialization denies before any builder call", rejected (runCountWork (materializeNatural 5000 {n=0}) 4096)),
   ("count materialization exact reservation boundary", case runCountWork (materializeNatural 8 {n=0}) 8 of
      Just (0, value) => sameSyntax value (naturalTerm 8)
      _ => False),
   ("canonical natural reads spend every successor", rejected (runCountWork (naturalOperand (naturalTerm 8 {n=0})) 7) &&
      runCountWork (naturalOperand (naturalTerm 8 {n=0})) 8 == Just (0, Just 8)),
   ("canonical octet reads charge before modulo wrapping", rejected (runCountWork (octetOperand (naturalTerm 258 {n=0})) 257) &&
      runCountWork (octetOperand (naturalTerm 258 {n=0})) 258 == Just (0, Just 2)),
   ("full-step scans charge canonical successor visits even when stuck", rejected (runCountWork (stepWith (naturalTerm 8 {n=0})) 7) &&
      case runCountWork (stepWith (naturalTerm 8 {n=0})) 8 of Just (0, Nothing) => True; _ => False),
   ("NatRec successor matching charges a visit", rejected (runCountWork (stepHeadWith (foldCount (NatSucc NatZero))) 0)),
   ("zero count needs only terminal inspection", exhausts 0 NatZero && succeeds 1 0 NatZero),
   ("zero length costs contraction plus terminal inspection", exhausts 1 (length 0) && succeeds 2 0 (length 0)),
   ("length count costs construction and later visits", exhausts 17 (length 8) && succeeds 18 8 (length 8)),
   ("canonical1024 counts retain ordinary visit cost", exhausts 1024 (naturalTerm 1024) && succeeds 1025 1024 (naturalTerm 1024)),
   ("length1024 count reserves construction from same ledger", exhausts 2049 (length 1024) && succeeds 2050 1024 (length 1024)),
   ("beta nested length shares ledger", let term = Apply (Lambda Linear BytesType (BytesLength (Variable FZ))) (bytes 8) in
      exhausts 18 term && succeeds 19 8 term),
   ("successor tail length shares ledger", exhausts 18 (NatSucc (length 8)) && succeeds 19 9 (NatSucc (length 8))),
   ("NatRec scrutinee visits and reductions share ledger", exhausts 50 (foldCount (length 8)) && succeeds 51 8 (foldCount (length 8))),
   ("BytesIndex payload reserves its unary octet before allocation", rejected (runCountWork (stepHeadWith (BytesIndex NatZero (BytesValue (fromList [255])) {n=0})) 254) &&
      exhausts 513 indexCount && succeeds 514 255 indexCount),
   ("demanded full-step operand cannot bypass materializer", rejected (runCountWork (stepHeadWith (BytesLengthIs (NatSucc (length 5000)) (bytes 0))) 4096)),
   ("octet full-step fallback cannot bypass materializer", let term = BytesLength (BytesOctet (length 5000)) in
      rejected (runCountWork (stepHeadWith term) 4096)),
   ("derived byte operands reserve before natural construction", exhausts 4096 (BytesLength (BytesAppend (bytes 3000) (bytes 3000)))),
   ("unused count branch stays lazy", succeeds 10 8 (BoolCase BoolTrue (naturalTerm 8) (length 5000))),
   ("unused beta argument stays lazy", succeeds 2 0 (Apply (Lambda Erased NatType NatZero) (length 5000))),
   ("irreducible count is not exhaustion", case decodeBinaryCount 1 (the (Term 0) BoolTrue) of Left CountExpectedNat => True; _ => False),
   ("unmetered length contraction is unchanged", case stepHead (length 8) of Just value => sameSyntax value (naturalTerm 8); _ => False)]
