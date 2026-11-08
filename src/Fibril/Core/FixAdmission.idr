-- Admission gate for Fix terms: extract call sites, then require a size-change
-- verdict. Unsupported syntax, inconclusive limits and rejections all refuse.
module Fibril.Core.FixAdmission

import Data.List
import Fibril.Core.Term
import Fibril.Termination.Extract
import Fibril.Termination.SizeChange

%default total

-- First call site (1-based) with no strictly smaller argument at all.
firstWithoutDecrease : Nat -> List Call -> Maybe Nat
firstWithoutDecrease _ [] = Nothing
firstWithoutDecrease i (edge :: rest) =
  if any (any (== Decreases)) edge.matrix then firstWithoutDecrease (S i) rest else Just i

-- With several nodes (the members of a mutual group) one call may legitimately shrink
-- nothing because it only forwards to a member that does. Blaming such a call would
-- mislead, so there the failing thing is a cycle of calls, not a call.
explain : Nat -> List Call -> String -> String
explain nodes edges why =
  if nodes > 1
    then "no argument decreases around every cycle of calls between the members (" ++ why ++ ")"
    else case firstWithoutDecrease 1 edges of
      Just i => "no argument decreases: recursive call " ++ show i ++ " of " ++ show (length edges) ++
                " passes nothing smaller than a parameter"
      Nothing => "no argument decreases along every recursive cycle: the calls do not combine into a decrease (" ++ why ++ ")"

-- True when the checker gave up on size, not on the program.
gaveUp : Production -> Bool
gaveUp (ClosureProduced _ (GraphInconclusive _)) = True
gaveUp (ProductionInconclusive _) = True
gaveUp _ = False

decide : Nat -> Nat -> List Call -> Either String ()
decide nodes arity edges = case produce (replicate nodes arity) edges of
  ClosureProduced _ GraphAccepted => Right ()
  ClosureProduced _ (GraphRejected why) => Left (explain nodes edges why)
  ClosureProduced _ (GraphInconclusive why) => Left ("size-change check inconclusive: " ++ why)
  ProductionInvalid why => Left why
  ProductionInconclusive why => Left why

||| Decide whether a recursive body may be treated as total. The checker has
||| already typed the body under a hypothetical unrestricted self; this gate
||| supplies the separate termination judgment. Failure is not a divergence proof.
|||
||| The finer, member-aware graph is a refinement: it accepts everything the merged one
||| does. If it only exceeds the checker's size limits, the merged graph decides instead,
||| so refining can never refuse a function that was admitted before.
public export
admitFixWith : FieldCounts -> Term n -> Term (S n) -> Either String ()
admitFixWith info ty body = do
  extraction <- extractFixWith info ty body
  let arity = arityOf ty
  if extraction.nodes > 1 && gaveUp (produce (replicate extraction.nodes arity) extraction.calls)
    then decide 1 arity extraction.coarse
    else decide extraction.nodes arity extraction.calls

||| Admission when no general data family is in scope.
public export
admitFix : Term n -> Term (S n) -> Either String ()
admitFix = admitFixWith noFamilies
