-- Sorted-list helpers for the reference DNF algorithms.
-- Engineering optimization, not a new algebra or a verified solver.
module Fibril.Foundation.DeMorgan.Sorted

import Data.List

%default total

adjacentUnique : Eq a => List a -> List a
adjacentUnique [] = []
adjacentUnique (x :: xs) = x :: go x xs
  where
    go : a -> List a -> List a
    go previous [] = []
    go previous (next :: rest) =
      if previous == next then go previous rest else next :: go next rest

||| Sort and remove duplicates in one subsequent linear pass.
||| The result is ascending and duplicate-free under a lawful Ord instance.
public export
canonicalSorted : Ord a => List a -> List a
canonicalSorted = adjacentUnique . sort

||| Linear merge-style subset check. BOTH inputs must already be ascending.
||| Callers establish this invariant through canonicalSorted. Unsorted inputs
||| are not validated and must not be passed to this internal solver helper.
public export
subsetSorted : Ord a => List a -> List a -> Bool
subsetSorted [] ys = True
subsetSorted (x :: xs) [] = False
subsetSorted (x :: xs) (y :: ys) =
  case compare x y of
    LT => False
    EQ => subsetSorted xs ys
    GT => subsetSorted (x :: xs) ys
