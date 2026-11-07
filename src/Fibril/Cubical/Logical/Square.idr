-- A checked, nondependent two-dimensional abstraction over the A fragment.
module Fibril.Cubical.Logical.Square

import Data.Fin
import Fibril.Cubical.Logical.Telescope
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Restriction

%default total

-- Body indices: j = 0, i = 1, then ambient dimensions. Each edge is
-- abstracted over the remaining dimension, at index 0.
insertI : Fin (S n) -> ScopedInterval (S (S n))
insertI FZ = Var FZ
insertI (FS x) = Var (FS (FS x))

insertJ : Fin (S n) -> ScopedInterval (S (S n))
insertJ x = Var (FS x)

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

admitted : Maybe Nat -> Bool
admitted Nothing = False
admitted (Just _) = True

||| Admit the whole input under one cap before weakening. Each subsequent
||| face conversion has its own bounded preflight; conversion is incomplete.
public export
checkSquare : {m, k, n : Nat} -> Nat -> Telescope m k -> Term m k (S (S n)) ->
              Term m k (S n) -> Term m k (S n) ->
              Term m k (S n) -> Term m k (S n) -> Result
checkSquare {m} {k} {n} budget ctx body i0 i1 j0 j1 =
  if not (m <= 12 && k <= 12 && n <= 10) then Exhausted else
  let input = do
        a <- contextNodes (min 16 budget) ctx
        b <- termNodes a body
        c <- termNodes b i0
        d <- termNodes c i1
        e <- termNodes d j0
        termNodes e j1 in
  if not (admitted input) then Exhausted else
  case convertRestricted budget (Under (SEndpoint (FS FZ) False)) ctx body (mapDims insertI i0) of
    Accepted => case convertRestricted budget (Under (SEndpoint (FS FZ) True)) ctx body (mapDims insertI i1) of
      Accepted => case convertRestricted budget (Under (SEndpoint FZ False)) ctx body (mapDims insertJ j0) of
        Accepted => convertRestricted budget (Under (SEndpoint FZ True)) ctx body (mapDims insertJ j1)
        other => other
      other => other
    other => other

export
data CheckedSquare : (ctx : Telescope m k) -> (body : Term m k (S (S n))) ->
                     (i0, i1, j0, j1 : Term m k (S n)) -> Type where
  MkCheckedSquare : CheckedSquare ctx body i0 i1 j0 j1

export
checkBoundSquare : {m, k, n : Nat} -> (budget : Nat) -> (ctx : Telescope m k) ->
                   (body : Term m k (S (S n))) -> (i0, i1, j0, j1 : Term m k (S n)) ->
                   Either Result (CheckedSquare ctx body i0 i1 j0 j1)
checkBoundSquare budget ctx body i0 i1 j0 j1 =
  case checkSquare budget ctx body i0 i1 j0 j1 of
    Accepted => Right MkCheckedSquare
    other => Left other
