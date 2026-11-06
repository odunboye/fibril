-- Checked pure indexing/slicing boundary; no stream capability.
module Fibril.Source.Primitive.Bytes

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Source.Global

%default total

indexCaseType : Term 0
indexCaseType = Pi Erased (Universe 0)
  (Pi Linear byteIndexResultType
    (Pi Unrestricted (Variable (FS FZ))
      (Pi Unrestricted (Pi Linear NatType (Variable (FS (FS (FS FZ)))))
        (Variable (FS (FS (FS FZ)))))))

indexCaseValue : Term 0
indexCaseValue = Lambda Erased (Universe 0)
  (Lambda Linear byteIndexResultType
    (Lambda Unrestricted (Variable (FS FZ))
      (Lambda Unrestricted (Pi Linear NatType (Variable (FS (FS (FS FZ)))))
        (VariantCase (Lambda Erased byteIndexResultType (Variable (FS (FS (FS (FS FZ))))))
          (Variable (FS (FS FZ))) [Variable (FS FZ), Variable FZ]))))

public export
bytePrimitiveGlobals : List GlobalDefinition
bytePrimitiveGlobals =
  [ GlobalWithQuantity Erased "ByteIndexResult" (Universe 0) byteIndexResultType
  , Global "primBytesIndex" (Pi Linear NatType (Pi Linear BytesType byteIndexResultType))
      (Lambda Linear NatType (Lambda Linear BytesType
        (BytesIndex (Variable (FS FZ)) (Variable FZ))))
  , Global "primBytesIndexCase" indexCaseType indexCaseValue
  , Global "primBytesSlice" (Pi Linear NatType (Pi Linear NatType (Pi Linear BytesType BytesType)))
      (Lambda Linear NatType (Lambda Linear NatType (Lambda Linear BytesType
        (BytesSlice (Variable (FS (FS FZ))) (Variable (FS FZ)) (Variable FZ)))))
  ]
