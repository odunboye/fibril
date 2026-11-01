-- Closed global definitions, not axioms or trusted typing certificates.
module Fibril.Source.Global

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term

%default total

||| Only closed unrestricted definitions are installed by the current prelude.
||| Resolution embeds checked-ascription applications, preserving declared types.
||| Ordinary checking still validates the entire resulting term; these are not axioms.
public export
record GlobalDefinition where
  constructor Global
  name : String
  declaredType : Term 0
  value : Term 0

public export
lookupGlobal : String -> List GlobalDefinition -> Maybe (Term 0)
lookupGlobal name [] = Nothing
lookupGlobal name (entry :: rest) =
  if name == entry.name
     then Just (Apply (Lambda Linear entry.declaredType (Variable FZ)) entry.value)
     else lookupGlobal name rest
