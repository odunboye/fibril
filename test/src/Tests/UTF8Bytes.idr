module Tests.UTF8Bytes

import Data.Fin
import Data.List
import Fibril.Data.Bytes
import Fibril.Source.UTF8
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Context
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Size
import Fibril.Core.ResourceAdmission
import Fibril.Elaboration.Expression.Scope
import Fibril.Elaboration.Expression.Conversion
import Fibril.Driver.Check

%default total

accepted : Term 0 -> Term 0 -> Bool
accepted term ty = case checkRuntime 1024 128 Empty term ty of
  Left _ => False
  Right _ => True

both : Term 0 -> Term 0 -> Bool
both term expected = case (normalize 32 term, weakHead 32 term) of
  (Normal a, HeadForm b) => sameSyntax a expected && sameSyntax b expected
  _ => False

valid : List (String, List Bits8)
valid = [("",[]), (pack [chr 0],[0]), ("A",[65]), ("λ",[206,187]),
  ("🌍",[240,159,140,141]), ("�",[239,191,189]),
  (pack [chr 0x7FF],[223,191]), (pack [chr 0x800],[224,160,128]),
  (pack [chr 0xD7FF],[237,159,191]), (pack [chr 0xE000],[238,128,128]),
  (pack [chr 0xFFFF],[239,191,191]), (pack [chr 0x10000],[240,144,128,128]),
  (pack [chr 0xFEFF],[239,187,191]), (pack [chr 0x10FFFF],[244,143,191,191])]

invalid : List (List Bits8)
invalid = [[128],[255],[192,128],[224,128,128],[237,160,128],
  [240,128,128,128],[244,144,128,128],[245,128,128,128],
  [194],[224,160],[240,144,128],[194,65],[224,160,65],[240,144,128,65]]

roundtrip : (String, List Bits8) -> Bool
roundtrip (text, bytes) =
  both (UTF8Encode (StringValue text))
    (VariantValue (utf8ResultType BytesType) 1 (Just (BytesValue (fromList bytes)))) &&
  both (UTF8Decode (BytesValue (fromList bytes)))
    (VariantValue (utf8ResultType StringType) 1 (Just (StringValue text))) &&
  case (encodeUTF8 text, decodeUTF8 bytes) of
    (Right encoded, Right decoded) => encoded == bytes && decoded == text
    _ => False

rejected : List Bits8 -> Bool
rejected bytes = both (UTF8Decode (BytesValue (fromList bytes)))
  (VariantValue (utf8ResultType StringType) 0 Nothing)

openTerms : List (Term 1)
openTerms = [UTF8Encode (Variable FZ), UTF8Decode (Variable FZ)]

sourceAccepted : String -> Bool
sourceAccepted source = case checkSource False source of
  Left _ => False
  Right _ => True

public export
checks : List (String, Bool)
checks =
  [("UTF8 codec matches scalar vectors in full/head reduction", all roundtrip valid),
   ("UTF8 malformed sequences fail without replacement", all rejected invalid),
   ("UTF8 encode result is explicit", accepted (UTF8Encode (StringValue "λ")) (utf8ResultType BytesType)),
   ("UTF8 decode result is explicit", accepted (UTF8Decode (BytesValue empty)) (utf8ResultType StringType)),
   ("UTF8 encode is not bare Bytes", not (accepted (UTF8Encode (StringValue "")) BytesType)),
   ("UTF8 decode is not bare String", not (accepted (UTF8Decode (BytesValue empty)) StringType)),
   ("UTF8 conversion checks operand types", not (accepted (UTF8Encode UnitValue) (utf8ResultType BytesType)) && not (accepted (UTF8Decode UnitValue) (utf8ResultType StringType))),
   ("UTF8 conversion transports scope", all (\term => sameSyntax (rename id term) term && sameSyntax (substituteTerm Variable term) term) openTerms),
   ("UTF8 conversion node accounting agrees", all (\term => coreNodes term == substitutionNodes (const 1) term) openTerms),
   ("UTF8 resource scan enters both operands", containsFileReference (the (Term 0) (UTF8Encode (FileHandleValue 1 0))) && containsFileReference (the (Term 0) (UTF8Decode (FileHandleValue 1 0)))),
   ("UTF8 encoding expansion admitted before allocation", not (guardedStepAdmitted (the (Term 0) (UTF8Encode (StringValue (pack (replicate 3000 'λ'))))))),
   ("UTF8 valid empty conversion is not failure", roundtrip ("", [])),
   ("UTF8 valid NUL conversion is not failure", roundtrip (pack [chr 0], [0])),
   ("UTF8 actual replacement character is preserved", roundtrip ("�", [239,191,189])),
   ("source UTF8 result requires an explicit case", not (sourceAccepted "main : Bytes\nmain = primUTF8Encode \"x\"")),
   ("source UTF8 success payload is consumed linearly", not (sourceAccepted "main : Nat\nmain = primUTF8Case Bytes Nat (primUTF8Encode \"x\") Zero (\\(1 b : Bytes) => Zero)")),
   ("source UTF8 case accepts a consuming handler", sourceAccepted "main : Nat\nmain = primUTF8Case Bytes Nat (primUTF8Encode \"λ\") Zero (\\(1 b : Bytes) => primBytesLength b)")]
