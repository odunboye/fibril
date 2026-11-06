-- Inert source descriptions; execution requires the separate binary runner.
module Fibril.Source.Primitive.Binary

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Source.Global

%default total

caseType : Term 0
caseType = Pi Erased (Universe 0) (Pi Linear byteReadResultType
  (Pi Unrestricted (Variable (FS FZ))
    (Pi Unrestricted (Pi Linear BytesType (Variable (FS (FS (FS FZ)))))
      (Variable (FS (FS (FS FZ)))))))

caseValue : Term 0
caseValue = Lambda Erased (Universe 0) (Lambda Linear byteReadResultType
  (Lambda Unrestricted (Variable (FS FZ))
    (Lambda Unrestricted (Pi Linear BytesType (Variable (FS (FS (FS FZ)))))
      (VariantCase (Lambda Erased byteReadResultType (Variable (FS (FS (FS (FS FZ))))))
        (Variable (FS (FS FZ))) [Variable (FS FZ), Variable FZ]))))

public export
binaryPrimitiveGlobals : List GlobalDefinition
binaryPrimitiveGlobals =
  [ GlobalWithQuantity Erased "ByteReadResult" (Universe 0) byteReadResultType
  , Global "primReadBytes" (Pi Linear NatType (IOType byteReadResultType))
      (Lambda Linear NatType (ReadBytes (Variable FZ)))
  , Global "primWriteBytes" (Pi Linear BytesType (IOType UnitType))
      (Lambda Linear BytesType (WriteBytes (Variable FZ)))
  , Global "primFlushBytes" (IOType UnitType) FlushBytes
  , Global "primByteReadCase" caseType caseValue
  ]
