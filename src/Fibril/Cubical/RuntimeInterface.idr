module Fibril.Cubical.RuntimeInterface

import Fibril.Core.Quantity
import Fibril.Core.Term

%default total

||| Experimental literal-interface admission, not general type conversion.
public export
data InterfaceError = InterfaceLimit | UnsupportedInterface

-- Private representation: no core payloads, definitions, dimensions or brands.
data Shape = UnitShape | BoolShape | ArrowShape Quantity Shape Shape

||| Opaque admitted literal interface. No typing/transport theorem is claimed.
export
data RuntimeInterface = Admitted Shape

-- A single allowance is threaded through both children. Each visited node
-- costs one before recursion/allocation. No normalization is performed.
parse : Nat -> Term n -> Either InterfaceError (Shape, Nat)
parse Z _ = Left InterfaceLimit
parse (S remaining) UnitType = Right (UnitShape, remaining)
parse (S remaining) BoolType = Right (BoolShape, remaining)
parse (S remaining) (Pi q domain codomain) = do
  (a, afterDomain) <- parse remaining domain
  (b, afterCodomain) <- parse afterDomain codomain
  Right (ArrowShape q a b, afterCodomain)
parse (S _) _ = Left UnsupportedInterface

||| Admit only literal Unit, Bool and recursively nondependent Pi interfaces.
||| All variables (including Pi-bound ones), effects, handles and other forms
||| reject. This is deliberately smaller than the proposed eventual bridge.
export
admitRuntimeInterface : Nat -> Term n -> Either InterfaceError RuntimeInterface
admitRuntimeInterface allowance term = do
  (shape, _) <- parse allowance term
  Right (Admitted shape)

compare : Nat -> Shape -> Shape -> Either InterfaceError (Bool, Nat)
compare Z _ _ = Left InterfaceLimit
compare (S remaining) UnitShape UnitShape = Right (True, remaining)
compare (S remaining) BoolShape BoolShape = Right (True, remaining)
compare (S remaining) (ArrowShape q a b) (ArrowShape r c d) =
  if q == r then do
    (sameDomain, afterDomain) <- compare remaining a c
    if sameDomain then compare afterDomain b d
      else Right (False, afterDomain)
  else Right (False, remaining)
compare (S remaining) _ _ = Right (False, remaining)

||| Bounded structural comparison, NOT ordinary directional compatibility or
||| logical equality. Both original inputs must be admitted before comparison,
||| even if an outer mismatch would otherwise suffice. The same node-work
||| allowance covers admission of both inputs and comparison. No logical or
||| ordinary reduction/checker is called; quantities remain significant.
export
compareRuntimeInterfaces : Nat -> Term n -> Term m -> Either InterfaceError Bool
compareRuntimeInterfaces allowance left right = do
  (a, afterLeft) <- parse allowance left
  (b, afterRight) <- parse afterLeft right
  (equal, _) <- compare afterRight a b
  Right equal
