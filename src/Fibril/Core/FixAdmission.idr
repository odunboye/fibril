-- Admission gate for Fix terms: extract call sites, then require a size-change
-- verdict. Unsupported syntax, inconclusive limits and rejections all refuse.
module Fibril.Core.FixAdmission

import Fibril.Core.Term
import Fibril.Termination.Extract
import Fibril.Termination.SizeChange

%default total

||| Decide whether a recursive body may be treated as total. The checker has
||| already typed the body under a hypothetical unrestricted self; this gate
||| supplies the separate termination judgment. Failure is not a divergence proof.
public export
admitFix : Term n -> Term (S n) -> Either String ()
admitFix ty body = do
  edges <- extractFix ty body
  case produce [arityOf ty] edges of
    ClosureProduced _ GraphAccepted => Right ()
    ClosureProduced _ (GraphRejected why) => Left ("no argument decreases along every recursive cycle: " ++ why)
    ClosureProduced _ (GraphInconclusive why) => Left ("size-change check inconclusive: " ++ why)
    ProductionInvalid why => Left why
    ProductionInconclusive why => Left why
