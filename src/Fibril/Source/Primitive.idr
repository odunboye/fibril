-- Small typed primitive boundary; library names such as putStrLn are not here.
module Fibril.Source.Primitive

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Data.Bytes
import Fibril.Source.Global
import Fibril.Source.Primitive.Input
import Fibril.Source.Primitive.Bytes
import Fibril.Source.Primitive.Resource

%default total

ioConstructor : Term 0
ioConstructor = Lambda Erased (Universe 0) (IOType (Variable FZ))

pureConstructor : Term 0
pureConstructor = Lambda Erased (Universe 0)
                    (Lambda Linear (Variable FZ) (IOPure (Variable FZ)))

bindConstructor : Term 0
bindConstructor =
  Lambda Erased (Universe 0) (Lambda Erased (Universe 0)
    (Lambda Linear (IOType (Variable (FS FZ)))
      (Lambda Linear
        (Pi Linear (Variable (FS (FS FZ))) (IOType (Variable (FS (FS FZ)))))
        (IOBind (Variable (FS (FS (FS FZ)))) (Variable (FS (FS FZ)))
                (Variable (FS FZ)) (Variable FZ)))))

natMotive : Term 0
natMotive = Pi Erased NatType (Universe 0)

-- The ambient context is [base, motive]; the step receives an erased
-- predecessor and one linear induction result.
natStep : Term 2
natStep = Pi Erased NatType
  (Pi Linear (Apply (Variable (FS (FS FZ))) (Variable FZ))
    (Apply (Variable (FS (FS (FS FZ)))) (NatSucc (Variable (FS FZ)))))

natRecType : Term 0
natRecType = Pi Erased natMotive
  (Pi Linear (Apply (Variable FZ) NatZero)
    (Pi Unrestricted natStep
      (Pi Linear NatType (Apply (Variable (FS (FS (FS FZ)))) (Variable FZ)))))

natRecValue : Term 0
natRecValue = Lambda Erased natMotive
  (Lambda Linear (Apply (Variable FZ) NatZero)
    (Lambda Unrestricted natStep
      (Lambda Linear NatType
        (NatRec (Variable (FS (FS (FS FZ)))) (Variable (FS (FS FZ)))
                (Variable (FS FZ)) (Variable FZ)))))

-- Runtime access to the predecessor requires unrestricted use of the count:
-- the successor contraction passes the predecessor to both the step and the
-- recursive call.
natRuntimeStep : Term 2
natRuntimeStep = Pi Unrestricted NatType
  (Pi Linear (Apply (Variable (FS (FS FZ))) (Variable FZ))
    (Apply (Variable (FS (FS (FS FZ)))) (NatSucc (Variable (FS FZ)))))

natRecWithType : Term 0
natRecWithType = Pi Erased natMotive
  (Pi Linear (Apply (Variable FZ) NatZero)
    (Pi Unrestricted natRuntimeStep
      (Pi Unrestricted NatType (Apply (Variable (FS (FS (FS FZ)))) (Variable FZ)))))

natRecWithValue : Term 0
natRecWithValue = Lambda Erased natMotive
  (Lambda Linear (Apply (Variable FZ) NatZero)
    (Lambda Unrestricted natRuntimeStep
      (Lambda Unrestricted NatType
        (NatRecRuntime (Variable (FS (FS (FS FZ)))) (Variable (FS (FS FZ)))
                       (Variable (FS FZ)) (Variable FZ)))))

||| Small-type interface: A/B : Type0. IOType itself preserves arbitrary levels.
public export
primitiveGlobals : List GlobalDefinition
primitiveGlobals =
  bytePrimitiveGlobals ++ resourcePrimitiveGlobals ++ inputPrimitiveGlobals ++
  [ GlobalWithQuantity Erased "Bytes" (Universe 0) BytesType
  , Global "primBytesEmpty" BytesType (BytesValue empty)
  , Global "primBytesOctetMod256" (Pi Linear NatType BytesType)
      (Lambda Linear NatType (BytesOctet (Variable FZ)))
  , Global "primBytesLength" (Pi Linear BytesType NatType)
      (Lambda Linear BytesType (BytesLength (Variable FZ)))
  , Global "primBytesAppend" (Pi Linear BytesType (Pi Linear BytesType BytesType))
      (Lambda Linear BytesType (Lambda Linear BytesType
        (BytesAppend (Variable (FS FZ)) (Variable FZ))))
  , GlobalWithQuantity Erased "Nat" (Universe 0) NatType
  , Global "Zero" NatType NatZero
  , Global "Succ" (Pi Linear NatType NatType) (Lambda Linear NatType (NatSucc (Variable FZ)))
  , Global "natRec" natRecType natRecValue
  , Global "natRecWith" natRecWithType natRecWithValue
  , Global "IO" (Pi Erased (Universe 0) (Universe 0)) ioConstructor
  , Global "primPure"
      (Pi Erased (Universe 0) (Pi Linear (Variable FZ) (IOType (Variable (FS FZ)))))
      pureConstructor
  , Global "primBind"
      (Pi Erased (Universe 0) (Pi Erased (Universe 0)
        (Pi Linear (IOType (Variable (FS FZ)))
          (Pi Linear
            (Pi Linear (Variable (FS (FS FZ))) (IOType (Variable (FS (FS FZ)))))
            (IOType (Variable (FS (FS FZ))))))))
      bindConstructor
  , Global "primStringAppend" (Pi Linear StringType (Pi Linear StringType StringType))
      (Lambda Linear StringType (Lambda Linear StringType
        (StringAppend (Variable (FS FZ)) (Variable FZ))))
  , Global "primStringEqual" (Pi Linear StringType (Pi Linear StringType BoolType))
      (Lambda Linear StringType (Lambda Linear StringType
        (StringEqual (Variable (FS FZ)) (Variable FZ))))
  , Global "primWriteLine" (Pi Linear StringType (IOType UnitType))
      (Lambda Linear StringType (WriteLine (Variable FZ)))
  ]
