module Tests.Network

import Data.Fin
import Data.List
import Fibril.Core.Context
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.EffectAdmission
import Fibril.Core.OutputAdmission
import Fibril.Driver.Native.Emit
import Fibril.Source.Global
import Fibril.Source.Primitive.Network

%default total

accepted : Either a b -> Bool
accepted (Right _) = True
accepted _ = False

stream : Term n
stream = Prim NetStreamTypeOp []

connectArgs : Term n
connectArgs = PairValue (networkArguments (networkInputs NetConnectOp)) (StringValue "127.0.0.1")
  (PairValue (networkArguments [Prim WordTypeOp [], Prim WordTypeOp []]) (wordTerm 5432)
    (PairValue (networkArguments [Prim WordTypeOp []]) (wordTerm 1000) UnitValue))

connect : Term n
connect = Prim NetConnectOp [connectArgs]

validGlobal : GlobalDefinition -> Bool
validGlobal entry = accepted (checkErased 512 1024 Empty entry.value entry.declaredType)

public export
checks : List (String, Bool)
checks =
  [ ("all socket primitive globals independently typecheck", all validGlobal networkPrimitiveGlobals)
  , ("connect is a typed inert IO description", accepted (checkRuntime 512 1024 Empty connect (IOType (networkResult stream))))
  , ("socket types have no source value constructor", not (accepted (checkErased 512 1024 Empty (wordTerm 1) stream)))
  , ("socket type expressions are not runtime values", not (accepted (checkRuntime 512 1024 Empty stream (Universe 0))))
  , ("duplicating a linear socket is rejected", not (accepted (checkRuntime 512 1024 Empty
      (Lambda Linear stream (PairValue (networkPair stream stream) (Variable FZ) (Variable FZ)))
      (Pi Linear stream (networkPair stream stream)))))
  , ("socket primitive arity is checked", not (accepted (inferErased 512 1024 Empty (Prim NetConnectOp []))))
  , ("socket primitive argument types are checked", not (accepted (inferErased 512 1024 Empty (Prim NetReadOp [UnitValue]))))
  , ("network effects require explicit runner", not (accepted (emitCheckedC connect)))
  , ("network scans find erased socket syntax", containsNetworkRequest {n=0} (Apply (Lambda Erased (Universe 0) UnitValue) stream))
  , ("network scans find dead operations", containsNetworkRequest {n=0} (BoolCase BoolTrue UnitValue connect))
  , ("network syntax is forbidden by binary runners", containsNonBinaryIO {n=0} connect)
  , ("network syntax is forbidden by console runners", containsBinaryRequest {n=0} connect)
  , ("JavaScript output profile rejects network syntax", not (outputOnly {n=0} False connect))
  , ("embedded output profile rejects network syntax", not (outputOnly {n=0} True connect))
  , ("network profile rejects dead console input", not (networkOnly {n=0} (BoolCase BoolTrue UnitValue ReadLine)))
  , ("network profile accepts original socket syntax", networkOnly {n=0} connect)
  ]
