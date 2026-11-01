module Tests.Pretty

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Pretty

%default total

||| Snapshot checks keep diagnostics and counterexample rendering consistent.
public export
checks : List (String, Bool)
checks =
  [ ("pretty universe", renderTerm (the (Term 0) (Universe 2)) == "Type2")
  , ("pretty bound index", renderTerm (the (Term 2) (Variable (FS FZ))) == "v1")
  , ("pretty explicit Pi", renderTerm
      (the (Term 0) (Pi Erased (Universe 0) (Variable FZ))) == "(Pi 0 Type0 v0)")
  , ("pretty explicit lambda", renderTerm
      (the (Term 0) (Lambda Linear (Universe 0) (Variable FZ))) == "(Lam 1 Type0 v0)")
  , ("pretty application preserves grouping", renderTerm
      (the (Term 1) (Apply (Variable FZ) (Apply (Variable FZ) (Variable FZ)))) ==
      "(v0 @ (v0 @ v0))")
  , ("pretty Show uses shared rendering",
      show (the (Term 0) (Universe 1)) == renderTerm (the (Term 0) (Universe 1)))
  ]
