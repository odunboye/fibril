-- Explicit scalar UTF-8 conversion, not a console or stream operation.
module Fibril.Source.Primitive.UTF8

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Source.Global

%default total

resultConstructor : Term 0
resultConstructor = Lambda Erased (Universe 0) (utf8ResultType (Variable FZ))

caseType : Term 0
caseType = Pi Erased (Universe 0) (Pi Erased (Universe 0)
  (Pi Linear (utf8ResultType (Variable (FS FZ)))
    (Pi Unrestricted (Variable (FS FZ))
      (Pi Unrestricted (Pi Linear (Variable (FS (FS (FS FZ)))) (Variable (FS (FS (FS FZ)))))
        (Variable (FS (FS (FS FZ))))))))

caseValue : Term 0
caseValue = Lambda Erased (Universe 0) (Lambda Erased (Universe 0)
  (Lambda Linear (utf8ResultType (Variable (FS FZ)))
    (Lambda Unrestricted (Variable (FS FZ))
      (Lambda Unrestricted (Pi Linear (Variable (FS (FS (FS FZ)))) (Variable (FS (FS (FS FZ)))))
        (VariantCase (Lambda Erased (utf8ResultType (Variable (FS (FS (FS (FS FZ))))))
          (Variable (FS (FS (FS (FS FZ))))))
          (Variable (FS (FS FZ))) [Variable (FS FZ), Variable FZ])))))

public export
utf8PrimitiveGlobals : List GlobalDefinition
utf8PrimitiveGlobals =
  [ GlobalWithQuantity Erased "UTF8Result" (Pi Erased (Universe 0) (Universe 0)) resultConstructor
  , Global "primUTF8Encode" (Pi Linear StringType (utf8ResultType BytesType))
      (Lambda Linear StringType (UTF8Encode (Variable FZ)))
  , Global "primUTF8Decode" (Pi Linear BytesType (utf8ResultType StringType))
      (Lambda Linear BytesType (UTF8Decode (Variable FZ)))
  , Global "primUTF8Case" caseType caseValue
  ]
