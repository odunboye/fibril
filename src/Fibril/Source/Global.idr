-- Closed global definitions, not axioms or trusted typing certificates.
module Fibril.Source.Global

import Fibril.Core.Term

%default total

||| Only closed unrestricted definitions are installed by the current prelude.
||| Resolution embeds values; ordinary checking still checks the resulting term.
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
  if name == entry.name then Just entry.value else lookupGlobal name rest
