-- Experimental first-order open endpoints in a well-founded path telescope.
module Fibril.Cubical.Logical.Telescope

import Data.Fin
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Restriction

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

-- Only reduce an application when the entire assumption entails its endpoint.
-- The variable case additionally permits the two endpoints to cover the face.
restricted : {n : Nat} -> Nat -> ScopedFace n -> Telescope m k -> Term m k n -> Term m k n -> Result
restricted Z _ _ _ _ = Exhausted
restricted (S fuel) face ctx a b =
  if holds (Under face) SBottom then Accepted else
  case (a, b) of
    (Tvar x, Tvar y) => if x == y then Accepted else Rejected
    (Tvar x, Tapp p r) => againstVariable fuel face ctx p r x
    (Tapp p r, Tvar x) => againstVariable fuel face ctx p r x
    (Tapp p r, Tapp q s) =>
      if p == q && intervalMatches face r s then Accepted else
      if holds (Under face) (scopedEndpoint r False) then
        restricted fuel face ctx (mapDims closedDim (endpoint ctx p False)) b
      else if holds (Under face) (scopedEndpoint r True) then
        restricted fuel face ctx (mapDims closedDim (endpoint ctx p True)) b
      else if holds (Under face) (scopedEndpoint s False) then
        restricted fuel face ctx a (mapDims closedDim (endpoint ctx q False))
      else if holds (Under face) (scopedEndpoint s True) then
        restricted fuel face ctx a (mapDims closedDim (endpoint ctx q True))
      else Rejected
  where
    intervalMatches : {n : Nat} -> ScopedFace n -> ScopedInterval n -> ScopedInterval n -> Bool
    intervalMatches phi r s = case restrictedIntervalEqual 12 phi r s of
      Accepted => True
      _ => False

    againstVariable : {n : Nat} -> Nat -> ScopedFace n -> Telescope m k -> Fin k -> ScopedInterval n -> Fin m -> Result
    againstVariable Z _ _ _ _ _ = Exhausted
    againstVariable (S f) phi tele p r x =
      let l = restricted f phi tele (mapDims closedDim (endpoint tele p False)) (Tvar x)
          h = restricted f phi tele (mapDims closedDim (endpoint tele p True)) (Tvar x)
          lf = case l of Accepted => scopedEndpoint r False; _ => SBottom
          hf = case h of Accepted => scopedEndpoint r True; _ => SBottom in
      if holds (Under phi) (SDisjunction lf hf) then Accepted else
      case (l, h) of
        (Exhausted, _) => Exhausted
        (_, Exhausted) => Exhausted
        _ => Rejected

||| Sufficient face-restricted conversion. Admission bounds the complete context,
||| face and terms before solver calls; fuel bounds endpoint comparison chains.
public export
convertRestricted : {m, k, n : Nat} -> Nat -> Restriction n -> Telescope m k -> Term m k n -> Term m k n -> Result
convertRestricted {m} {k} {n} budget (Under face) ctx a b =
  if not (m <= 12 && k <= 12 && n <= 12) then Exhausted else
  case contextNodes (min 12 budget) ctx >>= \f => faceNodes f face >>= \g => termNodes g a >>= \h => termNodes h b of
    Nothing => Exhausted
    Just _ => restricted 27 face ctx a b

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
