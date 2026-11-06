-- Source input boundary, expressed with existing checked finite variants.
module Fibril.Source.Primitive.Input

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Source.Global

%default total

-- Branch arguments are unrestricted: only one is selected at runtime. They
-- cannot capture linear ambient resources through unrestricted application.
readCaseType : Term 0
readCaseType = Pi Erased (Universe 0)
  (Pi Linear readResultType
    (Pi Unrestricted (Variable (FS FZ))
      (Pi Unrestricted (Pi Linear StringType (Variable (FS (FS (FS FZ)))))
        (Pi Unrestricted (Pi Linear StringType (Variable (FS (FS (FS (FS FZ))))))
          (Variable (FS (FS (FS (FS FZ)))))))))

readCaseValue : Term 0
readCaseValue = Lambda Erased (Universe 0)
  (Lambda Linear readResultType
    (Lambda Unrestricted (Variable (FS FZ))
      (Lambda Unrestricted (Pi Linear StringType (Variable (FS (FS (FS FZ)))))
        (Lambda Unrestricted (Pi Linear StringType (Variable (FS (FS (FS (FS FZ))))))
          (VariantCase
            (Lambda Erased readResultType (Variable (FS (FS (FS (FS (FS FZ)))))))
            (Variable (FS (FS (FS FZ))))
            [Variable (FS (FS FZ)), Variable (FS FZ), Variable FZ])))))

public export
inputPrimitiveGlobals : List GlobalDefinition
inputPrimitiveGlobals =
  [ GlobalWithQuantity Erased "ReadResult" (Universe 0) readResultType
  , Global "primReadLine" (IOType readResultType) ReadLine
  , Global "primReadCase" readCaseType readCaseValue
  ]
