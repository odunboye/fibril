-- Experimental checked paths in the first-order telescope fragment.
module Fibril.Cubical.Logical.ReusablePath

import Data.Fin
import Fibril.Cubical.Logical.Telescope
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Restriction

%default total

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

liftDim : Fin n -> ScopedInterval (S n)
liftDim i = Var (FS i)

export
data CheckedPath : (ctx : Telescope m k) -> (body : Term m k (S n)) ->
                   (left, right : Term m k n) -> Type where
  MkCheckedPath : CheckedPath ctx body left right

||| Checks each boundary under its face, including open endpoint expressions.
export
checkPath : {m, k, n : Nat} -> (budget : Nat) -> (ctx : Telescope m k) ->
            (body : Term m k (S n)) -> (left, right : Term m k n) ->
            Either Result (CheckedPath ctx body left right)
checkPath {m} {k} {n} budget ctx body left right =
  if not (m <= 12 && k <= 12 && n <= 11) then Left Exhausted else
  case contextNodes (min 12 budget) ctx >>= \f => termNodes f body >>= \g => termNodes g left >>= \h => termNodes h right of
    Nothing => Left Exhausted
    Just _ => case convertRestricted budget (Under (SEndpoint FZ False)) ctx body (mapDims liftDim left) of
      Accepted => case convertRestricted budget (Under (SEndpoint FZ True)) ctx body (mapDims liftDim right) of
        Accepted => Right MkCheckedPath
        other => Left other
      other => Left other

instantiate : ScopedInterval n -> Fin (S n) -> ScopedInterval n
instantiate r FZ = r
instantiate r (FS i) = Var i

-- Count the substituted syntax before constructing it, including each copy of r.
substitutedIntervalNodes : {n : Nat} -> Nat -> ScopedInterval n -> ScopedInterval (S n) -> Maybe Nat
substitutedIntervalNodes Z r Zero = Nothing
substitutedIntervalNodes (S f) r Zero = Just f
substitutedIntervalNodes Z r One = Nothing
substitutedIntervalNodes (S f) r One = Just f
substitutedIntervalNodes f r (Var i) = case i of
  FZ => intervalNodes f r
  FS j => case f of
    Z => Nothing
    S g => Just g
substitutedIntervalNodes Z r (Reverse x) = Nothing
substitutedIntervalNodes (S f) r (Reverse x) = substitutedIntervalNodes f r x
substitutedIntervalNodes Z r (Meet x y) = Nothing
substitutedIntervalNodes (S f) r (Meet x y) = substitutedIntervalNodes f r x >>= \g => substitutedIntervalNodes g r y
substitutedIntervalNodes Z r (Join x y) = Nothing
substitutedIntervalNodes (S f) r (Join x y) = substitutedIntervalNodes f r x >>= \g => substitutedIntervalNodes g r y

substitutedTermNodes : {n : Nat} -> Nat -> ScopedInterval n -> Term m k (S n) -> Maybe Nat
substitutedTermNodes Z r _ = Nothing
substitutedTermNodes (S f) r (Tvar _) = Just f
substitutedTermNodes (S f) r (Tapp _ x) = substitutedIntervalNodes f r x

||| The witness fixes the context and body; application is syntactic substitution.
||| Input and resulting term are admitted under a shared cap, without conversion.
export
applyPath : {m, k, n : Nat} -> (budget : Nat) ->
            {ctx : Telescope m k} -> {body : Term m k (S n)} ->
            {left, right : Term m k n} -> CheckedPath ctx body left right ->
            ScopedInterval n -> Either Result (Term m k n)
applyPath {m} {k} {n} budget {ctx} {body} _ r =
  if not (m <= 12 && k <= 12 && n <= 11) then Left Exhausted else
  case contextNodes (min 12 budget) ctx >>= \f => termNodes f body >>= \g => intervalNodes g r of
    Nothing => Left Exhausted
    Just _ => case substitutedTermNodes (min 12 budget) r body of
      Nothing => Left Exhausted
      Just _ => Right (mapDims (instantiate r) body)
