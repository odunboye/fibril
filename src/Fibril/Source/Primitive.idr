-- Small typed primitive boundary; library names such as putStrLn are not here.
module Fibril.Source.Primitive

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Source.Global
import Fibril.Source.Primitive.Input

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

||| Small-type interface: A/B : Type0. IOType itself preserves arbitrary levels.
public export
primitiveGlobals : List GlobalDefinition
primitiveGlobals =
  inputPrimitiveGlobals ++
  [ Global "IO" (Pi Erased (Universe 0) (Universe 0)) ioConstructor
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
