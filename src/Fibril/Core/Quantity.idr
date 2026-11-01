module Fibril.Core.Quantity

%default total

||| Syntactic quantities. Cubical usage rules are not defined here yet.
public export
data Quantity = Erased | Linear | Unrestricted

public export
Eq Quantity where
  Erased == Erased = True
  Linear == Linear = True
  Unrestricted == Unrestricted = True
  _ == _ = False

public export
Show Quantity where
  show Erased = "0"
  show Linear = "1"
  show Unrestricted = "unrestricted"
