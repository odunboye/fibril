module Tests.ByteRanges

import Data.Fin
import Data.List
import Fibril.Data.Bytes
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Context
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Size
import Fibril.Core.ResourceAdmission
import Fibril.Elaboration.Expression.Scope
import Fibril.Elaboration.Expression.Payload
import Fibril.Elaboration.Expression.Conversion
import Fibril.Driver.Check

%default total

accepted : Term 0 -> Term 0 -> Bool
accepted term ty = case checkRuntime 1024 128 Empty term ty of
  Left _ => False
  Right _ => True

normal : Term 0 -> Term 0 -> Bool
normal term expected = case normalize 64 term of
  Normal result => sameSyntax result expected
  _ => False

head : Term 0 -> Term 0 -> Bool
head term expected = case weakHead 64 term of
  HeadForm result => sameSyntax result expected
  _ => False

both : Term 0 -> Term 0 -> Bool
both term expected = normal term expected && head term expected

found : Nat -> Term n
found n = VariantValue byteIndexResultType 1 (Just (naturalTerm n))

missing : Term n
missing = VariantValue byteIndexResultType 0 Nothing

sample : Term n
sample = BytesValue (fromList [0,255,128,13,10])

betaOne : Term 0
betaOne = NatSucc (Apply (Lambda Linear NatType (Variable FZ)) NatZero)

allOctets : Bytes
allOctets = fromList (map cast (the (List Nat) [0..255]))

indexAgrees : Nat -> Bool
indexAgrees n = both (BytesIndex (naturalTerm n) (BytesValue allOctets))
  (if n < 256 then found n else missing)

openTerms : List (Term 1)
openTerms = [BytesLengthIs (Variable FZ) sample, BytesLengthIs NatZero (Variable FZ), BytesIndex (Variable FZ) sample, BytesIndex NatZero (Variable FZ),
  BytesSlice (Variable FZ) NatZero sample, BytesSlice NatZero (Variable FZ) sample,
  BytesSlice NatZero NatZero (Variable FZ)]

forged : List (Term 0)
forged = [BytesLengthIs (FileHandleValue 1 0) sample, BytesLengthIs NatZero (FileHandleValue 1 0), BytesIndex (FileHandleValue 1 0) sample,
  BytesIndex NatZero (FileHandleValue 1 0),
  BytesSlice (FileHandleValue 1 0) NatZero sample,
  BytesSlice NatZero (FileHandleValue 1 0) sample,
  BytesSlice NatZero NatZero (FileHandleValue 1 0)]

sourceAccepted : String -> Bool
sourceAccepted source = case checkSource False source of
  Left _ => False
  Right _ => True

nest : Nat -> Term n -> Term n
nest Z term = term
nest (S n) term = Lambda Erased UnitType (weaken (nest n term))

public export
checks : List (String, Bool)
checks =
  [("length predicate compares without a unary result", all (\n => both (BytesLengthIs (naturalTerm n) sample) (if n == 5 then BoolTrue else BoolFalse)) (the (List Nat) [0..257])),
   ("length predicate handles empty", both (BytesLengthIs NatZero (BytesValue empty)) BoolTrue && both (BytesLengthIs (naturalTerm 1) (BytesValue empty)) BoolFalse),
   ("length predicate returns checked Bool", accepted (BytesLengthIs (naturalTerm 5) sample) BoolType && not (accepted (BytesLengthIs NatZero sample) NatType)),
   ("length predicate rejects wrong operands", not (accepted (BytesLengthIs UnitValue sample) BoolType) && not (accepted (BytesLengthIs NatZero UnitValue) BoolType)),
   ("length predicate reduces successor tails", both (BytesLengthIs betaOne (BytesValue (fromList [255]))) BoolTrue),
   ("length predicate does not grow nodes", guardedStepAdmitted (nest 200 (the (Term 0) (BytesLengthIs (naturalTerm 5) sample)))),
   ("source length predicate consumes linear bytes", sourceAccepted "check : (1 b : Bytes) -> Bool\ncheck = \\(1 b : Bytes) => primBytesLengthIs Zero b\nmain : Bool\nmain = check primBytesEmpty"),
   ("length predicate rejects linear reuse", not (sourceAccepted "check : (1 b : Bytes) -> Bool\ncheck = \\(1 b : Bytes) => if primBytesLengthIs Zero b then primBytesLengthIs Zero b else False\nmain : Bool\nmain = check primBytesEmpty")),
   ("length predicate payload estimate scans bytes", payloadSize (the (Term 0) (BytesLengthIs NatZero sample)) == 5),
   ("index preserves every octet and rejects both end indices", all indexAgrees (the (List Nat) [0..257])),
   ("empty bytes index is missing", both (BytesIndex NatZero (BytesValue empty)) missing),
   ("index NUL is found, not missing", both (BytesIndex NatZero sample) (found 0)),
   ("index FF is found, not a sentinel", both (BytesIndex (naturalTerm 1) sample) (found 255)),
   ("index requires Nat and Bytes", not (accepted (BytesIndex UnitValue sample) byteIndexResultType) && not (accepted (BytesIndex NatZero UnitValue) byteIndexResultType)),
   ("index result has explicit alternatives", accepted (BytesIndex NatZero sample) byteIndexResultType),
   ("index is not a bare Nat", not (accepted (BytesIndex NatZero sample) NatType)),
   ("slice requires both natural arguments", not (accepted (BytesSlice UnitValue NatZero sample) BytesType) && not (accepted (BytesSlice NatZero UnitValue sample) BytesType)),
   ("slice requires Bytes", not (accepted (BytesSlice NatZero NatZero UnitValue) BytesType)),
   ("slice is checked Bytes", accepted (BytesSlice NatZero (naturalTerm 2) sample) BytesType),
   ("zero count is empty", both (BytesSlice NatZero NatZero sample) (BytesValue empty)),
   ("slice preserves NUL FF invalid UTF8", both (BytesSlice NatZero (naturalTerm 3) sample) (BytesValue (fromList [0,255,128]))),
   ("slice offset is measured in bytes", both (BytesSlice (naturalTerm 1) (naturalTerm 2) sample) (BytesValue (fromList [255,128]))),
   ("slice truncates count", both (BytesSlice (naturalTerm 3) (naturalTerm 255) sample) (BytesValue (fromList [13,10]))),
   ("slice at end is empty", both (BytesSlice (naturalTerm 5) (naturalTerm 2) sample) (BytesValue empty)),
   ("slice beyond end is empty", both (BytesSlice (naturalTerm 255) (naturalTerm 255) sample) (BytesValue empty)),
   ("slice of empty is empty", both (BytesSlice (naturalTerm 255) (naturalTerm 255) (BytesValue empty)) (BytesValue empty)),
   ("index forces reducible successor payload", both (BytesIndex betaOne sample) (found 255)),
   ("slice forces reducible successor payloads", both (BytesSlice betaOne betaOne sample) (BytesValue (fromList [255]))),
   ("octet head reduction forces successor payload", both (BytesOctet betaOne) (BytesValue (fromList [1]))),
   ("range node counts agree", all (\term => coreNodes term == substitutionNodes (const 1) term) openTerms),
   ("range nodes transport variables", all (\term => sameSyntax (rename id term) term && sameSyntax (substituteTerm Variable term) term) openTerms),
   ("resource scan enters all range operands", all containsFileReference forged),
   ("index result expansion is guarded before allocation", not (guardedStepAdmitted (nest 200 (the (Term 0) (BytesIndex NatZero (BytesValue (fromList [255]))))))),
   ("missing index does not reserve a found payload", guardedStepAdmitted (nest 200 (the (Term 0) (BytesIndex NatZero (BytesValue empty))))),
   ("range payload estimate includes bytes", payloadSize (the (Term 0) (BytesSlice NatZero NatZero sample)) == 5),
   ("source accepts explicit missing/found case", sourceAccepted "main : Nat\nmain = primBytesIndexCase Nat (primBytesIndex Zero primBytesEmpty) Zero (\\(1 n : Nat) => n)"),
   ("source rejects discarded found payload", not (sourceAccepted "main : Nat\nmain = primBytesIndexCase Nat (primBytesIndex Zero primBytesEmpty) Zero (\\(1 n : Nat) => Zero)")),
   ("source linear slice consumes bytes once", sourceAccepted "take : (1 b : Bytes) -> Bytes\ntake = \\(1 b : Bytes) => primBytesSlice Zero Zero b\nmain : Bytes\nmain = take primBytesEmpty")]
