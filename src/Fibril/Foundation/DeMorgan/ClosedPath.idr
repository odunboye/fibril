-- An isolated, deliberately incomplete experiment; not the Fibril core checker.
module Fibril.Foundation.DeMorgan.ClosedPath

import Data.Fin
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.PathSyntax
import Fibril.Foundation.DeMorgan.Scope

%default total

||| Failure to decide within the budget is distinct from invalid syntax or boundaries.
public export
data PathCheck = Accepted | Rejected | Exhausted

||| Check the constant-Boolean fragment of Path Bool left right.
||| One unit of fuel is charged for inspecting the abstraction, one for its body,
||| and one for comparing both boundaries. No annotations are trusted.
public export
checkConstantPath : Nat -> PathExpr 0 -> Bool -> Bool -> PathCheck
checkConstantPath 0 _ _ _ = Exhausted
checkConstantPath (S fuel) (Abstract body) left right = checkBody fuel body
  where
    checkBody : Nat -> PathExpr 1 -> PathCheck
    checkBody 0 _ = Exhausted
    checkBody (S fuel) (Literal value) = checkBoundaries fuel value
      where
        checkBoundaries : Nat -> Bool -> PathCheck
        checkBoundaries 0 _ = Exhausted
        checkBoundaries (S _) value =
          if value == left && value == right then Accepted else Rejected
    checkBody (S _) _ = Rejected
checkConstantPath (S _) _ _ _ = Rejected

||| Evaluate a closed endpoint application only after checking its path.
||| This does not implement general path application or neutral-path reduction.
public export
data EndpointResult = EndpointValue Bool | InvalidEndpoint | EndpointExhausted

public export
runEndpoint : Nat -> PathExpr 0 -> Bool -> Bool -> EndpointResult
runEndpoint 0 _ _ _ = EndpointExhausted
runEndpoint (S fuel) (Apply path Zero) left right =
  case checkConstantPath fuel path left right of
    Accepted => EndpointValue left
    Rejected => InvalidEndpoint
    Exhausted => EndpointExhausted
runEndpoint (S fuel) (Apply path One) left right =
  case checkConstantPath fuel path left right of
    Accepted => EndpointValue right
    Rejected => InvalidEndpoint
    Exhausted => EndpointExhausted
runEndpoint (S _) _ _ _ = InvalidEndpoint
