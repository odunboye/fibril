-- Operator fixity metadata: parsing-order data only, never a typing rule.
module Fibril.Source.Fixity

%default total

public export
data Assoc = LeftAssoc | RightAssoc | NoAssoc

public export
Eq Assoc where
  LeftAssoc == LeftAssoc = True
  RightAssoc == RightAssoc = True
  NoAssoc == NoAssoc = True
  _ == _ = False

||| Binding strength 0..9 (higher binds tighter) and how equal-strength chains group.
public export
record Fixity where
  constructor MkFixity
  assoc : Assoc
  level : Nat

public export
Eq Fixity where
  a == b = a.assoc == b.assoc && a.level == b.level

||| Operators without a declaration group left at the tightest level, like backtick calls.
public export
defaultFixity : Fixity
defaultFixity = MkFixity LeftAssoc 9

public export
maxLevel : Nat
maxLevel = 9
