module Tests.CoreBytes

import Data.Fin
import Data.List
import Data.String
import Fibril.Data.Bytes
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Context
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.ResourceAdmission
import Fibril.Core.EffectAdmission
import Fibril.Core.Size
import Fibril.Elaboration.Expression.Scope
import Fibril.Elaboration.Expression.Payload
import Fibril.Elaboration.Expression.Conversion
import Fibril.Driver.Check
import Fibril.Driver.Native.Emit

%default total

accepted : Term 0 -> Term 0 -> Bool
accepted term ty = case checkRuntime 1024 128 Empty term ty of
  Left _ => False
  Right _ => True

sourceAccepted : String -> Bool
sourceAccepted source = case checkSource False source of
  Left _ => False
  Right _ => True

normal : Term 0 -> Term 0 -> Bool
normal term expected = case normalize 32 term of
  Normal result => sameSyntax result expected
  _ => False

head : Term 0 -> Term 0 -> Bool
head term expected = case weakHead 32 term of
  HeadForm result => sameSyntax result expected
  _ => False

sample : Term 0
sample = BytesAppend (BytesOctet NatZero) (BytesValue (fromList [255,13,10,128]))

literalOutput : Term 0
literalOutput = WriteLine (NatRec (Lambda Erased NatType StringType) (StringValue "")
  (Lambda Erased NatType (Lambda Linear StringType (StringAppend (StringValue "x") (Variable FZ))))
  (BytesLength (BytesValue (fromList [0,255,128,13,10]))))

literalEmission : Either String String -> Bool
literalEmission (Left _) = False
literalEmission (Right code) = isInfixOf "0,255,128,13,10" code && isInfixOf "f_bytes_literal(" code && isInfixOf "f_bytes_length(" code

openTerms : List (Term 1)
openTerms = [BytesShare (Variable FZ), BytesType, BytesValue (fromList [0,255]), BytesLength (Variable FZ),
             BytesOctet (Variable FZ), BytesAppend (Variable FZ) (BytesValue empty)]

shareDuplicate : Term 0
shareDuplicate = Lambda Linear BytesType
  (BoxCase (Lambda Erased (BoxType Unrestricted BytesType) BytesType)
    (BytesShare (Variable FZ))
    (Lambda Unrestricted BytesType (BytesAppend (Variable FZ) (Variable FZ))))

public export
checks : List (String, Bool)
checks =
  [("byte sharing consumes immutable input into an unrestricted box", accepted (BytesShare (BytesValue (fromList [0,255]))) (BoxType Unrestricted BytesType)),
   ("byte sharing is not a generic String promotion", not (accepted (BytesShare (StringValue "x")) (BoxType Unrestricted BytesType))),
   ("byte sharing cannot promote IO descriptions", not (accepted (BytesShare FlushBytes) (BoxType Unrestricted BytesType))),
   ("byte sharing cannot promote resource handles", not (accepted (BytesShare (FileHandleValue 1 0)) (BoxType Unrestricted BytesType))),
   ("byte sharing permits explicit pure duplication", accepted shareDuplicate (Pi Linear BytesType BytesType)),
   ("full sharing reduction preserves octets", normal (Apply shareDuplicate (BytesValue (fromList [0,255]))) (BytesValue (fromList [0,255,0,255]))),
   ("head sharing reduction preserves octets", head (Apply shareDuplicate (BytesValue (fromList [0,255]))) (BytesValue (fromList [0,255,0,255]))),
   ("byte sharing still scans hidden file references", containsFileReference (the (Term 0) (BytesShare (FileHandleValue 1 0)))),
   ("byte sharing still scans hidden binary requests", containsBinaryRequest (the (Term 0) (BytesShare FlushBytes))),
   ("byte sharing does not hide text IO", containsNonBinaryIO (the (Term 0) (BytesShare (WriteLine (StringValue "hidden"))))),
   ("checked native byte literals preserve decimal octets", literalEmission (emitCheckedC literalOutput)),
   ("checked interactive native byte literals preserve decimal octets", literalEmission (emitCheckedInteractiveC 512 128 literalOutput)),
   ("Bytes literals check separately from String", accepted (BytesValue (fromList [0,255,128])) BytesType),
   ("Bytes cannot be used as text", not (accepted (BytesValue empty) StringType)),
   ("String cannot be used as Bytes", not (accepted (StringValue "") BytesType)),
   ("Bytes append is checked", accepted sample BytesType),
   ("Bytes length returns Nat", accepted (BytesLength sample) NatType),
   ("Bytes octet requires Nat", not (accepted (BytesOctet (StringValue "0")) BytesType)),
   ("Bytes length requires Bytes", not (accepted (BytesLength (StringValue "")) NatType)),
   ("Bytes append checks both operands", not (accepted (BytesAppend (BytesValue empty) UnitValue) BytesType)),
   ("full Bytes normalization preserves all octets", normal sample (BytesValue (fromList [0,255,13,10,128]))),
   ("head Bytes normalization preserves all octets", head sample (BytesValue (fromList [0,255,13,10,128]))),
   ("full Bytes length counts octets", normal (BytesLength sample) (naturalTerm 5)),
   ("head Bytes length counts octets", head (BytesLength sample) (naturalTerm 5)),
   ("octet modulo wraps 256 to NUL", normal (BytesOctet (naturalTerm 256)) (BytesValue (fromList [0]))),
   ("octet modulo preserves FF", head (BytesOctet (naturalTerm 255)) (BytesValue (fromList [255]))),
   ("bytes syntax transports structurally", all (\term => sameSyntax (rename id term) term && sameSyntax (substituteTerm Variable term) term) openTerms),
   ("byte node counts agree with substitution estimator", all (\term => coreNodes term == substitutionNodes (const 1) term) openTerms),
   ("byte literal payload is counted", payloadSize (the (Term 0) (BytesValue (fromList [0,255,128]))) == 3),
   ("oversize byte literal conversion is rejected", not (guardedStepAdmitted (the (Term 0) (BytesValue (fromList (replicate 8193 0)))))),
   ("length expansion is admitted before allocation", not (guardedStepAdmitted (the (Term 0) (BytesLength (BytesValue (fromList (replicate 512 0))))))),
   ("small length expansion is admitted", guardedStepAdmitted (the (Term 0) (BytesLength (BytesValue (fromList [0,255]))))),
   ("resource scan enters both append operands", containsFileReference (the (Term 0) (BytesAppend (FileHandleValue 1 0) (BytesValue empty))) && containsFileReference (the (Term 0) (BytesAppend (BytesValue empty) (FileHandleValue 1 0)))),
   ("resource scan enters length and octet", containsFileReference (the (Term 0) (BytesLength (FileHandleValue 1 0))) && containsFileReference (the (Term 0) (BytesOctet (FileHandleValue 1 0)))),
   ("source can construct NUL and count binary values", sourceAccepted "main : Nat\nmain = primBytesLength (primBytesAppend (primBytesOctetMod256 Zero) (primBytesOctetMod256 (Succ Zero)))"),
   ("source cannot print bytes through text API", not (sourceAccepted "main : IO Unit\nmain = putStrLn primBytesEmpty")),
   ("source rejects duplicate linear byte use", not (sourceAccepted "copy : (1 b : Bytes) -> Bytes\ncopy = \\(1 b : Bytes) => primBytesAppend b b\nmain : Bytes\nmain = primBytesEmpty")),
   ("source accepts one linear byte use", sourceAccepted "copy : (1 b : Bytes) -> Bytes\ncopy = \\(1 b : Bytes) => primBytesAppend b primBytesEmpty\nmain : Bytes\nmain = copy primBytesEmpty")]
