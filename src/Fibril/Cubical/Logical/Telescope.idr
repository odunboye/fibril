-- Experimental first-order open endpoints in a well-founded path telescope.
module Fibril.Cubical.Logical.Telescope

import Data.Fin
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

||| A-terms; path names are scoped by the length of the surrounding telescope.
public export
data Term : Nat -> Nat -> Nat -> Type where
  Tvar : Fin m -> Term m k n
  Tapp : Fin k -> ScopedInterval n -> Term m k n

||| A declaration can mention only earlier paths and no dimensions.
public export
data Telescope : Nat -> Nat -> Type where
  Empty : Telescope m 0
  Extend : Telescope m k -> Term m k 0 -> Term m k 0 -> Telescope m (S k)

public export
mapDims : (Fin n -> ScopedInterval d) -> Term m k n -> Term m k d
mapDims env (Tvar x) = Tvar x
mapDims env (Tapp p r) = Tapp p (substituteScoped env r)

weakenPath : Term m k n -> Term m (S k) n
weakenPath (Tvar x) = Tvar x
weakenPath (Tapp p r) = Tapp (FS p) r

-- Repeated weakening preserves references to older declarations.
endpoint : Telescope m k -> Fin k -> Bool -> Term m k 0
endpoint (Extend ctx l r) FZ side = weakenPath (if side then r else l)
endpoint (Extend ctx l r) (FS p) side = weakenPath (endpoint ctx p side)

closedDim : Fin 0 -> ScopedInterval n
closedDim x impossible

sameInterval : ScopedInterval n -> ScopedInterval n -> Bool
sameInterval Zero Zero = True
sameInterval One One = True
sameInterval (Var x) (Var y) = x == y
sameInterval (Reverse x) (Reverse y) = sameInterval x y
sameInterval (Meet x y) (Meet a b) = sameInterval x a && sameInterval y b
sameInterval (Join x y) (Join a b) = sameInterval x a && sameInterval y b
sameInterval _ _ = False

termNodes : Nat -> Term m k n -> Maybe Nat
termNodes Z _ = Nothing
termNodes (S f) (Tvar _) = Just f
termNodes (S f) (Tapp _ r) = intervalNodes f r

contextNodes : Nat -> Telescope m k -> Maybe Nat
contextNodes f Empty = Just f
contextNodes Z (Extend _ _ _) = Nothing
contextNodes (S f) (Extend ctx l r) = do
  a <- contextNodes f ctx
  b <- termNodes a l
  termNodes b r

-- Fuel bounds unfolding even if a caller supplies a very large telescope.
reduce : Nat -> Telescope m k -> Term m k n -> Maybe (Term m k n)
reduce Z _ _ = Nothing
reduce (S f) ctx (Tapp p Zero) = reduce f ctx (mapDims closedDim (endpoint ctx p False))
reduce (S f) ctx (Tapp p One) = reduce f ctx (mapDims closedDim (endpoint ctx p True))
reduce (S f) _ term = Just term

||| Unrestricted, syntactic conversion after literal endpoint reduction only.
||| The combined input and context cap bounds unfolding and generated terms.
public export
convert : {m, k, n : Nat} -> Nat -> Telescope m k -> Term m k n -> Term m k n -> Result
convert {m} {k} {n} budget ctx a b =
  if not (m <= 12 && k <= 12 && n <= 12) then Exhausted else
  case contextNodes (min 12 budget) ctx >>= \f => termNodes f a >>= \g => termNodes g b of
    Nothing => Exhausted
    Just _ => case (reduce 13 ctx a, reduce 13 ctx b) of
      (Just (Tvar x), Just (Tvar y)) => if x == y then Accepted else Rejected
      (Just (Tapp p r), Just (Tapp q s)) => if p == q && sameInterval r s then Accepted else Rejected
      (Just _, Just _) => Rejected
      _ => Exhausted

||| Check both literal faces of a dimension abstraction against open terms.
public export
checkBoundary : {m, k, n : Nat} -> Nat -> Telescope m k -> Term m k (S n) -> Term m k n -> Term m k n -> Result
checkBoundary {m} {k} {n} budget ctx body l r =
  if not (m <= 12 && k <= 12 && n <= 11) then Exhausted else
  case contextNodes (min 12 budget) ctx >>= \f => termNodes f body >>= \g => termNodes g l >>= \h => termNodes h r of
    Nothing => Exhausted
    Just _ => case convert budget ctx (mapDims zero body) l of
      Accepted => convert budget ctx (mapDims one body) r
      other => other
  where
    zero : Fin (S n) -> ScopedInterval n
    zero FZ = Zero
    zero (FS i) = Var i
    one : Fin (S n) -> ScopedInterval n
    one FZ = One
    one (FS i) = Var i
