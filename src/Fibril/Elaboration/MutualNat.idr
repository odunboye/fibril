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
