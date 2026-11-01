-- Usage coefficient arithmetic and a proposed local binder policy. Not a typing
-- checker; see docs/core-draft.md for unresolved judgments.
module Fibril.Core.Quantity

%default total

||| Usage coefficients. Full typing and cubical usage rules remain unimplemented.
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

||| Combine uses in simultaneously evaluated subterms.
||| Saturation deliberately loses counts above one.
public export
add : Quantity -> Quantity -> Quantity
add Erased q = q
add q Erased = q
add _ _ = Unrestricted

||| Scale an argument's usage by its binder coefficient.
public export
multiply : Quantity -> Quantity -> Quantity
multiply Erased _ = Erased
multiply _ Erased = Erased
multiply Linear q = q
multiply q Linear = q
multiply Unrestricted Unrestricted = Unrestricted

||| Exact-use policy for the proposed initial computational fragment.
||| This is not a general subusage relation or a complete typing rule.
public export
allows : (binder : Quantity) -> (observed : Quantity) -> Bool
allows Erased observed = observed == Erased
allows Linear observed = observed == Linear
allows Unrestricted _ = True
