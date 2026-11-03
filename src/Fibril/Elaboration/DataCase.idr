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
||| No schema/name authority, payload unpacking or source syntax is provided.
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
