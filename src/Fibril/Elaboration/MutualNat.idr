-- A finite translation, not general recursive-group or SCT admission.
module Fibril.Elaboration.MutualNat

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term

%default total

private
state : Term n
state = Pi Linear BoolType BoolType

private
literal : Bool -> Term n
literal True = BoolTrue
literal False = BoolFalse

private
payloadState : Term n
payloadState = Pi Linear BoolType (Pi Linear BoolType BoolType)

||| Preserve authored identity separately: Bool eta is not definitional equality.
public export
data PayloadBase = KeepPayload | TruthTable Bool Bool

private
payloadBase : PayloadBase -> Fin n -> Term n
payloadBase KeepPayload position = Variable position
payloadBase (TruthTable yes no) position = BoolCase (Variable position) (literal yes) (literal no)

||| The state is selector -> payload -> Bool. Payload ownership enters AFTER
||| the recursor, so its repeated step captures no linear payload.
public export
payloadWorker : PayloadBase -> PayloadBase -> Bool -> Bool -> Bool -> Term 0
payloadWorker base0 base1 target0 target1 entry =
  Lambda Linear NatType
    (Lambda Linear BoolType
      (Apply (Apply (NatRec
        (Lambda Erased NatType payloadState)
        (Lambda Linear BoolType (Lambda Linear BoolType
          (BoolCase (Variable (FS FZ))
            (payloadBase base0 FZ)
            (payloadBase base1 FZ))))
        (Lambda Erased NatType (Lambda Linear payloadState
          (Lambda Linear BoolType (Lambda Linear BoolType
            (BoolCase (Variable (FS FZ))
              (Apply (Apply (Variable (FS (FS FZ))) (literal target0)) (Variable FZ))
              (Apply (Apply (Variable (FS (FS FZ))) (literal target1)) (Variable FZ)))))))
        (Variable (FS FZ))) (literal entry)) (Variable FZ)))

||| Both bases and targets are included in each closed worker. True denotes
||| member zero; False denotes member one. The predecessor is erased and the
||| induction result is consumed once in each exclusive selector branch.
public export
worker : Bool -> Bool -> Bool -> Bool -> Bool -> Term 0
worker base0 base1 target0 target1 entry =
  Lambda Linear NatType
    (Apply (NatRec
      (Lambda Erased NatType state)
      (Lambda Linear BoolType (BoolCase (Variable FZ) (literal base0) (literal base1)))
      (Lambda Erased NatType (Lambda Linear state (Lambda Linear BoolType
        (BoolCase (Variable FZ)
          (Apply (Variable (FS FZ)) (literal target0))
          (Apply (Variable (FS FZ)) (literal target1))))))
      (Variable FZ)) (literal entry))
