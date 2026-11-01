-- Usage coefficient arithmetic and a proposed local binder policy. Not a typing
-- checker; see docs/core-draft.md for unresolved judgments.
-- Theory: ATKEY18 sec. 2.1.1 (zero/one/many semiring); MCBRIDE16 (erasure motivation).
-- Alternative permission join is our local design; law/proof scope: docs/alternatives.md.
-- Bibliography and limitations: docs/references.md.
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

||| Least common permission for alternative observations (not simultaneous use).
||| 0 and 1 are incomparable; only unrestricted permission admits both.
public export
joinQuantity : Quantity -> Quantity -> Quantity
joinQuantity Erased Erased = Erased
joinQuantity Linear Linear = Linear
joinQuantity _ _ = Unrestricted

||| Exact-use policy for the proposed initial computational fragment.
||| This is not a general subusage relation or a complete typing rule.
public export
allows : (binder : Quantity) -> (observed : Quantity) -> Bool
allows Erased observed = observed == Erased
allows Linear observed = observed == Linear
allows Unrestricted _ = True

||| Exact permission characterization of the finite alternative join.
||| This proves a local coefficient law, not term subject reduction.
public export
joinAllows : (permission, left, right : Quantity) ->
  allows permission (joinQuantity left right) =
    (allows permission left && allows permission right)
joinAllows Erased Erased Erased = Refl
joinAllows Erased Erased Linear = Refl
joinAllows Erased Erased Unrestricted = Refl
joinAllows Erased Linear Erased = Refl
joinAllows Erased Linear Linear = Refl
joinAllows Erased Linear Unrestricted = Refl
joinAllows Erased Unrestricted Erased = Refl
joinAllows Erased Unrestricted Linear = Refl
joinAllows Erased Unrestricted Unrestricted = Refl
joinAllows Linear Erased Erased = Refl
joinAllows Linear Erased Linear = Refl
joinAllows Linear Erased Unrestricted = Refl
joinAllows Linear Linear Erased = Refl
joinAllows Linear Linear Linear = Refl
joinAllows Linear Linear Unrestricted = Refl
joinAllows Linear Unrestricted Erased = Refl
joinAllows Linear Unrestricted Linear = Refl
joinAllows Linear Unrestricted Unrestricted = Refl
joinAllows Unrestricted _ _ = Refl
