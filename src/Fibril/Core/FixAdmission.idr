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

explain : List Call -> String -> String
explain edges why = case firstWithoutDecrease 1 edges of
  Just i => "no argument decreases: recursive call " ++ show i ++ " of " ++ show (length edges) ++
            " passes nothing smaller than a parameter"
  Nothing => "no argument decreases along every recursive cycle: the calls do not combine into a decrease (" ++ why ++ ")"

||| Decide whether a recursive body may be treated as total. The checker has
||| already typed the body under a hypothetical unrestricted self; this gate
||| supplies the separate termination judgment. Failure is not a divergence proof.
public export
admitFix : Term n -> Term (S n) -> Either String ()
admitFix ty body = do
  edges <- extractFix ty body
  case produce [arityOf ty] edges of
    ClosureProduced _ GraphAccepted => Right ()
    ClosureProduced _ (GraphRejected why) => Left (explain edges why)
    ClosureProduced _ (GraphInconclusive why) => Left ("size-change check inconclusive: " ++ why)
    ProductionInvalid why => Left why
    ProductionInconclusive why => Left why
