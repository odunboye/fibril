-- Candidate core assembly only: never a checker, parser or typing certificate.
module Fibril.Elaboration.DataCase

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term

%default total

||| Assemble a direct nominal/variant case in the caller's context. The supplied
||| type, shape, motive and branches are all untrusted raw core terms. Branches
||| are already positional and must include any payload-binding lambdas. The
||| ordinary core checker must independently validate the entire resulting term.
||| No schema/name authority or source syntax is provided.
public export
assembleDataCase : Term n -> Term n -> Term n -> Term n -> List (Term n) -> Term n
assembleDataCase nominal shape motive scrutinee branches =
  NominalCase motive scrutinee
    (Lambda Linear shape
      (VariantCase
        (Lambda Erased (weaken shape)
          (Apply (rename (FS . FS) motive)
            (NominalValue (rename (FS . FS) nominal) (Variable FZ))))
        (Variable FZ)
        (map weaken branches)))

||| Assemble one branch for a constructor whose payload is a dependent pair.
||| `fields` is the caller's already-constructed curried two-field branch;
||| the checker validates its binders against the pair's actual quantities and
||| dependent domains. `tag`, nominal type and shape are untrusted raw inputs.
||| This is a candidate builder, not source pattern binding or a certificate.
public export
assemblePairPayloadBranch : Term n -> Term n -> Nat -> Term n -> Term n -> Term n -> Term n
assemblePairPayloadBranch nominal shape tag payload motive fields =
  Lambda Linear payload
    (PairCase
      (Lambda Erased (weaken payload)
        (Apply (rename (FS . FS) motive)
          (NominalValue (rename (FS . FS) nominal)
            (VariantValue (rename (FS . FS) shape) tag (Just (Variable FZ))))))
      (Variable FZ)
      (weaken fields))
