-- Opaque, linear TCP capability descriptions. Only emit-c-network executes them.
module Fibril.Source.Primitive.Network

import Data.Fin
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Source.Global

%default total

pack : List (Term n, Term n) -> Term n
pack [] = UnitValue
pack ((ty, value) :: rest) = PairValue
  (networkPair ty (networkArguments (map fst rest))) value (pack rest)

curryType : Nat -> List (Term n) -> Term n -> Term n
curryType _ [] result = result
curryType (S fuel) (ty :: rest) result = Pi Linear ty (curryType fuel (map weaken rest) (weaken result))

curryType Z _ result = result

curryValue : Nat -> PrimOp -> List (Term n) -> List (Term n, Term n) -> Term n
curryValue _ op [] args = Prim op [pack args]
curryValue (S fuel) op (ty :: rest) args = Lambda Linear ty
  (curryValue fuel op (map weaken rest) (map (\(a, b) => (weaken a, weaken b)) args ++ [(weaken ty, Variable FZ)]))

curryValue Z op _ args = Prim op [pack args]

operation : String -> PrimOp -> GlobalDefinition
operation name op = Global name (curryType 3 (networkInputs op) (IOType (networkOutput op)))
  (curryValue 3 op (networkInputs op) [])

public export
networkPrimitiveGlobals : List GlobalDefinition
networkPrimitiveGlobals =
  [ GlobalWithQuantity Erased "Socket" (Universe 0) (Prim NetStreamTypeOp [])
  , GlobalWithQuantity Erased "Listener" (Universe 0) (Prim NetListenerTypeOp [])
  , GlobalWithQuantity Erased "NetError" (Universe 0) networkError
  , GlobalWithQuantity Erased "NetReadResult" (Universe 0) networkReadResult
  , GlobalWithQuantity Erased "NetResult" (Pi Erased (Universe 0) (Universe 0))
      (Lambda Erased (Universe 0) (networkResult (Variable FZ)))
  , operation "primNetConnect" NetConnectOp
  , operation "primNetListen" NetListenOp
  , operation "primNetAccept" NetAcceptOp
  , operation "primNetRead" NetReadOp
  , operation "primNetWriteAll" NetWriteOp
  , operation "primNetClose" NetCloseOp
  , operation "primNetCloseListener" NetCloseListenerOp
  , operation "primNetLocalPort" NetLocalPortOp
  , operation "primNetShutdownWrite" NetShutdownWriteOp
  , GlobalWithQuantity Erased "SocketRead" (Universe 0) (networkOutput NetReadOp)
  , GlobalWithQuantity Erased "SocketWrite" (Universe 0) (networkOutput NetWriteOp)
  , GlobalWithQuantity Erased "SocketAccept" (Universe 0) (networkOutput NetAcceptOp)
  , GlobalWithQuantity Erased "ListenerPort" (Universe 0) (networkOutput NetLocalPortOp)
  , GlobalWithQuantity Erased "SocketShutdown" (Universe 0) (networkOutput NetShutdownWriteOp)
  , Global "primNetWordToString" (Pi Linear (Prim WordTypeOp []) StringType)
      (Lambda Linear (Prim WordTypeOp []) (Prim WordToStringOp [Variable FZ]))
  , Global "primNetResultCase" (Pi Erased (Universe 0) (Pi Erased (Universe 0) (Pi Linear (networkResult (Variable (FS (FZ)))) (Pi Unrestricted (Pi Linear networkError (Variable (FS (FS (FZ))))) (Pi Unrestricted (Pi Linear (Variable (FS (FS (FS (FZ))))) (Variable (FS (FS (FS (FZ)))))) (Variable (FS (FS (FS (FZ))))))))))
      (Lambda Erased (Universe 0) (Lambda Erased (Universe 0) (Lambda Linear (networkResult (Variable (FS (FZ)))) (Lambda Unrestricted (Pi Linear networkError (Variable (FS (FS (FZ))))) (Lambda Unrestricted (Pi Linear (Variable (FS (FS (FS (FZ))))) (Variable (FS (FS (FS (FZ)))))) (VariantCase (Lambda Erased (networkResult (Variable (FS (FS (FS (FS (FZ))))))) (Variable (FS (FS (FS (FS (FZ))))))) (Variable (FS (FS (FZ)))) [(Variable (FS (FZ))), (Variable (FZ))]))))))
  , Global "primNetReadCase" (Pi Erased (Universe 0) (Pi Linear networkReadResult (Pi Unrestricted (Variable (FS (FZ))) (Pi Unrestricted (Pi Linear BytesType (Variable (FS (FS (FS (FZ)))))) (Pi Unrestricted (Pi Linear networkError (Variable (FS (FS (FS (FS (FZ))))))) (Variable (FS (FS (FS (FS (FZ)))))))))))
      (Lambda Erased (Universe 0) (Lambda Linear networkReadResult (Lambda Unrestricted (Variable (FS (FZ))) (Lambda Unrestricted (Pi Linear BytesType (Variable (FS (FS (FS (FZ)))))) (Lambda Unrestricted (Pi Linear networkError (Variable (FS (FS (FS (FS (FZ))))))) (VariantCase (Lambda Erased networkReadResult (Variable (FS (FS (FS (FS (FS (FZ)))))))) (Variable (FS (FS (FS (FZ))))) [(Variable (FS (FS (FZ)))), (Variable (FS (FZ))), (Variable (FZ))]))))))
  ]
