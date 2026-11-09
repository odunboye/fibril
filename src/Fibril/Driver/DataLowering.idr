-- Shared representation lowering for checked data constructors/cases.
module Fibril.Driver.DataLowering

import Data.Fin
import Data.List
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.DataDecl

%default total

-- General recursive data has no runtime representation of its own. A constructor is a lambda
-- chain over its parameters (erased) and fields that builds a variant value, tagged by the
-- constructor index, whose payload is the fields as right-nested pairs; a case is a variant
-- case whose branches unpack that nest. The existing native variant and pair values do the work.

-- The quantities of a constructor type's binders after its parameters, in order.
public export
fieldQuantities : Nat -> Term n -> List Quantity
fieldQuantities Z (Pi q _ rest) = q :: fieldQuantities Z rest
fieldQuantities (S k) (Pi _ _ rest) = fieldQuantities k rest
fieldQuantities _ _ = []

-- Field `j` (1-based) of `m` is the variable m - j counting from the newest binder.
fieldVariable : {n : Nat} -> Nat -> Nat -> Maybe (Term n)
fieldVariable m j = map Variable (natToFin (minus m j) n)

pairNest : {n : Nat} -> Nat -> Nat -> List Quantity -> Maybe (Term n)
pairNest m j [] = Nothing
pairNest m j [q] = fieldVariable m j
pairNest m j [q1, q2] = do
  a <- fieldVariable m j
  b <- fieldVariable m (S j)
  Just (PairValue (Sigma q1 q2 (Universe 0) (Universe 0)) a b)
pairNest m j (q1 :: rest) = do
  a <- fieldVariable m j
  b <- pairNest m (S j) rest
  Just (PairValue (Sigma q1 Unrestricted (Universe 0) (Universe 0)) a b)

-- The constructor as a lambda chain mirroring its Pi type: one lambda per parameter and per
-- field, ending in the variant value built from the fields in the innermost scope.
public export
buildConstructor : {n : Nat} -> (index : Nat) -> (leading : Nat) -> (quantities : List Quantity) -> Term n -> Maybe (Term n)
buildConstructor index leading quantities chain = go leading chain
  where
    goFields : {m : Nat} -> Term m -> Maybe (Term m)
    goFields (Pi q domain rest) = map (Lambda q domain) (goFields rest)
    goFields _ = case quantities of
      [] => Just (VariantValue (Universe 0) index Nothing)
      _ => map (\payload => VariantValue (Universe 0) index (Just payload)) (pairNest (length quantities) 1 quantities)
    go : Nat -> {m : Nat} -> Term m -> Maybe (Term m)
    go Z term = goFields term
    go (S k) (Pi q domain rest) = map (Lambda q domain) (go k rest)
    go (S _) _ = Nothing

-- A branch takes the fields one at a time; the variant case hands it one payload. With two or
-- more fields the payload is a pair nest, so the branch is wrapped to unpack it.
unpackBranch : List Quantity -> Term n -> Term n -> Term n
unpackBranch [] applied payload = applied
unpackBranch [q] applied payload = Apply applied payload
unpackBranch [q1, q2] applied payload =
  PairCase NatType payload (Lambda q1 (Universe 0) (Lambda q2 (Universe 0)
    (Apply (Apply (weaken (weaken applied)) (Variable (FS FZ))) (Variable FZ))))
unpackBranch (q1 :: rest) applied payload =
  PairCase NatType payload (Lambda q1 (Universe 0) (Lambda Unrestricted (Universe 0)
    (unpackBranch rest (Apply (weaken (weaken applied)) (Variable (FS FZ))) (Variable FZ))))

wrapBranch : List Quantity -> Term n -> Term n
wrapBranch [] branch = branch
wrapBranch [q] branch = branch
wrapBranch quantities branch = Lambda Linear (Universe 0) (unpackBranch quantities (weaken branch) (Variable FZ))

public export
wrapBranches : DataDecl -> Nat -> List (Term n) -> Maybe (List (Term n))
wrapBranches decl index [] = Just []
wrapBranches decl index (branch :: rest) = do
  chain <- constructorType decl index
  following <- wrapBranches decl (S index) rest
  Just (wrapBranch (fieldQuantities (parameterCount decl) chain) branch :: following)
