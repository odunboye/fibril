-- A checked, nondependent two-dimensional abstraction over the A fragment.
module Fibril.Cubical.Logical.Square

import Data.Fin
import Fibril.Cubical.Logical.Telescope
import Fibril.Cubical.Logical.ReusablePath

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

-- Count substitutions before mapDims constructs any copies of the replacement.
subIntervalNodes : Nat -> (Nat -> Fin n -> Maybe Nat) -> ScopedInterval n -> Maybe Nat
subIntervalNodes f env (Var i) = env f i
subIntervalNodes Z env _ = Nothing
subIntervalNodes (S f) env Zero = Just f
subIntervalNodes (S f) env One = Just f
subIntervalNodes (S f) env (Reverse x) = subIntervalNodes f env x
subIntervalNodes (S f) env (Meet x y) = subIntervalNodes f env x >>= \g => subIntervalNodes g env y
subIntervalNodes (S f) env (Join x y) = subIntervalNodes f env x >>= \g => subIntervalNodes g env y

subTermNodes : Nat -> (Nat -> Fin n -> Maybe Nat) -> Term m k n -> Maybe Nat
subTermNodes Z env _ = Nothing
subTermNodes (S f) env (Tvar _) = Just f
subTermNodes (S f) env (Tapp _ x) = subIntervalNodes f env x

||| Instantiate the remaining dimension of a square edge.
||| This pure substitution is not an admission check.
public export
instantiateSquareEdge : ScopedInterval n -> Fin (S n) -> ScopedInterval n
instantiateSquareEdge r FZ = r
instantiateSquareEdge r (FS x) = Var x

||| Fix i while retaining j as the path binder.
public export
fixSquareI : ScopedInterval n -> Fin (S (S n)) -> ScopedInterval (S n)
fixSquareI r FZ = Var FZ
fixSquareI r (FS FZ) = substituteScoped (\x => Var (FS x)) r
fixSquareI r (FS (FS x)) = Var (FS x)

||| Fix j while retaining i as the path binder.
public export
fixSquareJ : ScopedInterval n -> Fin (S (S n)) -> ScopedInterval (S n)
fixSquareJ r FZ = substituteScoped (\x => Var (FS x)) r
fixSquareJ r (FS x) = Var x

oneNode : Nat -> Maybe Nat
oneNode Z = Nothing
oneNode (S f) = Just f

countAt : ScopedInterval n -> Nat -> Fin (S n) -> Maybe Nat
countAt r f FZ = intervalNodes f r
countAt r f (FS x) = oneNode f

countI : ScopedInterval n -> Nat -> Fin (S (S n)) -> Maybe Nat
countI r f FZ = oneNode f
countI r f (FS FZ) = intervalNodes f r
countI r f (FS (FS x)) = oneNode f

countJ : ScopedInterval n -> Nat -> Fin (S (S n)) -> Maybe Nat
countJ r f FZ = intervalNodes f r
countJ r f (FS x) = oneNode f

||| Apply one square dimension and independently recheck the resulting path.
||| Both preflights use a fixed 32-node ceiling and the caller's allowance;
||| checkPath separately applies its own smaller admission cap and allowance.
||| Rejected means the sufficient checker could not prove the boundaries.
public export
data SquareDirection = FixI | FixJ

export
applySquare : {m, k, n : Nat} -> (budget : Nat) -> (direction : SquareDirection) ->
              {ctx : Telescope m k} -> {body : Term m k (S (S n))} ->
              {i0, i1, j0, j1 : Term m k (S n)} ->
              CheckedSquare ctx body i0 i1 j0 j1 -> (r : ScopedInterval n) ->
              Either Result (case direction of
                FixI => CheckedPath ctx (mapDims (fixSquareI r) body) (mapDims (instantiateSquareEdge r) j0) (mapDims (instantiateSquareEdge r) j1)
                FixJ => CheckedPath ctx (mapDims (fixSquareJ r) body) (mapDims (instantiateSquareEdge r) i0) (mapDims (instantiateSquareEdge r) i1))
applySquare {m} {k} {n} budget direction {ctx} {body} {i0} {i1} {j0} {j1} witness r =
  if not (m <= 12 && k <= 12 && n <= 10) then Left Exhausted else
  let input = do
        a <- contextNodes (min 32 budget) ctx
        b <- termNodes a body
        c <- termNodes b i0
        d <- termNodes c i1
        e <- termNodes d j0
        f <- termNodes e j1
        intervalNodes f r in
  if not (admitted input) then Left Exhausted else
  case direction of
    FixI => case (do a <- contextNodes (min 32 budget) ctx
                     b <- subTermNodes a (countI r) body
                     c <- subTermNodes b (countAt r) j0
                     subTermNodes c (countAt r) j1) of
      Nothing => Left Exhausted
      Just _ => checkPath budget ctx (mapDims (fixSquareI r) body) (mapDims (instantiateSquareEdge r) j0) (mapDims (instantiateSquareEdge r) j1)
    FixJ => case (do a <- contextNodes (min 32 budget) ctx
                     b <- subTermNodes a (countJ r) body
                     c <- subTermNodes b (countAt r) i0
                     subTermNodes c (countAt r) i1) of
      Nothing => Left Exhausted
      Just _ => checkPath budget ctx (mapDims (fixSquareJ r) body) (mapDims (instantiateSquareEdge r) i0) (mapDims (instantiateSquareEdge r) i1)
