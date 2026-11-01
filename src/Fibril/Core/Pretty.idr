-- Stable diagnostic rendering of ordinary core syntax, not surface elaboration.
-- Nameless binding background: DEBRUIJN72; see docs/references.md.
module Fibril.Core.Pretty

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term

%default total

||| Render explicit core syntax using newest-first variable indices.
||| Parentheses preserve tree structure; this is not accepted source syntax.
||| Output preserves annotations/quantities and does not evaluate terms.
public export
renderTerm : Term n -> String
renderTerm (Variable i) = "v" ++ show (finToNat i)
renderTerm (Universe level) = "Type" ++ show level
renderTerm UnitType = "Unit"
renderTerm UnitValue = "()"
renderTerm (Pi q domain body) =
  "(Pi " ++ show q ++ " " ++ renderTerm domain ++ " " ++ renderTerm body ++ ")"
renderTerm (Lambda q domain body) =
  "(Lam " ++ show q ++ " " ++ renderTerm domain ++ " " ++ renderTerm body ++ ")"
renderTerm (Apply function argument) =
  "(" ++ renderTerm function ++ " @ " ++ renderTerm argument ++ ")"

renderTerm (UnitCase scrutinee body) =
  "(CaseUnit " ++ renderTerm scrutinee ++ " " ++ renderTerm body ++ ")"

||| Shared representation for diagnostics, examples, and shrinking counterexamples.
public export
Show (Term n) where
  show = renderTerm
