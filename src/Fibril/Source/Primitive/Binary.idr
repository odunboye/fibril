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

-- LoopStep and LoopResult deliberately share an ordinary structural shape.
loopAliasType : Term 0
loopAliasType = Pi Erased (Universe 0) (Pi Erased (Universe 0) (Universe 0))

loopAliasValue : Term 0
loopAliasValue = Lambda Erased (Universe 0) (Lambda Erased (Universe 0)
  (loopVariantType (Variable (FS FZ)) (Variable FZ)))

loopConstructorType : Bool -> Term 0
loopConstructorType done = Pi Erased (Universe 0) (Pi Erased (Universe 0)
  (Pi Linear (if done then Variable FZ else Variable (FS FZ))
    (loopVariantType (Variable (FS (FS FZ))) (Variable (FS FZ)))))

loopConstructorValue : Bool -> Term 0
loopConstructorValue done = Lambda Erased (Universe 0) (Lambda Erased (Universe 0)
  (Lambda Linear (if done then Variable FZ else Variable (FS FZ))
    (VariantValue (loopVariantType (Variable (FS (FS FZ))) (Variable (FS FZ)))
      (if done then 0 else 1) (Just (Variable FZ)))))

loopCaseBodyType : Term n -> Term n -> Term n -> Term n
loopCaseBodyType s r a = Pi Linear (loopVariantType s r)
  (Pi Unrestricted (Pi Linear (weaken r) (weaken (weaken a)))
    (Pi Unrestricted (Pi Linear (weaken (weaken s)) (weaken (weaken (weaken a))))
      (weaken (weaken (weaken a)))))

loopCaseType : Term 0
loopCaseType = Pi Erased (Universe 0) (Pi Erased (Universe 0)
  (Pi Erased (Universe 0)
    (loopCaseBodyType (Variable (FS (FS FZ))) (Variable (FS FZ)) (Variable FZ))))

loopCaseValue : Term 0
loopCaseValue = Lambda Erased (Universe 0)
  (Lambda Erased (Universe 0)
    (Lambda Erased (Universe 0)
      (Lambda Linear (loopVariantType (Variable (FS (FS FZ))) (Variable (FS FZ)))
        (Lambda Unrestricted (Pi Linear (Variable (FS (FS FZ))) (Variable (FS (FS FZ))))
          (Lambda Unrestricted (Pi Linear (Variable (FS (FS (FS (FS FZ))))) (Variable (FS (FS (FS FZ)))))
            (VariantCase
              (Lambda Erased (loopVariantType (Variable (FS (FS (FS (FS (FS FZ)))))) (Variable (FS (FS (FS (FS FZ))))))
                (Variable (FS (FS (FS (FS FZ))))))
              (Variable (FS (FS FZ))) [(Variable (FS FZ)), (Variable FZ)]))))))

iterateType : Term 0
iterateType = Pi Erased (Universe 0) (Pi Erased (Universe 0)
  (Pi Unrestricted NatType
    (Pi Unrestricted (binaryStepType (Variable (FS (FS FZ))) (Variable (FS FZ)))
      (Pi Linear (Variable (FS (FS (FS FZ))))
        (IOType (loopVariantType (Variable (FS (FS (FS (FS FZ)))))
                                 (Variable (FS (FS (FS FZ))))))))))

iterateValue : Term 0
iterateValue = Lambda Erased (Universe 0) (Lambda Erased (Universe 0)
  (Lambda Unrestricted NatType
    (Lambda Unrestricted (binaryStepType (Variable (FS (FS FZ))) (Variable (FS FZ)))
      (Lambda Linear (Variable (FS (FS (FS FZ))))
        (IterateBinary (Variable (FS (FS (FS (FS FZ)))))
          (Variable (FS (FS (FS FZ)))) (Variable (FS (FS FZ)))
          (Variable (FS FZ)) (Variable FZ))))))

public export
binaryPrimitiveGlobals : List GlobalDefinition
binaryPrimitiveGlobals =
  [ GlobalWithQuantity Erased "ByteReadResult" (Universe 0) byteReadResultType
  , Global "primReadBytes" (Pi Linear NatType (IOType byteReadResultType))
      (Lambda Linear NatType (ReadBytes (Variable FZ)))
  , Global "primWriteBytes" (Pi Linear BytesType (IOType UnitType))
      (Lambda Linear BytesType (WriteBytes (Variable FZ)))
  , Global "primFlushBytes" (IOType UnitType) FlushBytes
  , Global "primRejectBytes" (IOType UnitType) RejectBytes
  , Global "primByteReadCase" caseType caseValue
  , GlobalWithQuantity Erased "LoopStep" loopAliasType loopAliasValue
  , GlobalWithQuantity Erased "LoopResult" loopAliasType loopAliasValue
  , Global "primLoopDone" (loopConstructorType True) (loopConstructorValue True)
  , Global "primLoopContinue" (loopConstructorType False) (loopConstructorValue False)
  , Global "primLoopFinished" (loopConstructorType True) (loopConstructorValue True)
  , Global "primLoopExhausted" (loopConstructorType False) (loopConstructorValue False)
  , Global "primLoopStepCase" loopCaseType loopCaseValue
  , Global "primLoopResultCase" loopCaseType loopCaseValue
  , Global "primIterateBinary" iterateType iterateValue
  ]
