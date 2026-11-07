-- Sorted-list helpers for the reference DNF algorithms.
-- Engineering optimization, not a new algebra or a verified solver.
module Fibril.Foundation.DeMorgan.Sorted

import Data.List

%default total

adjacentUniqueGo : Eq a => a -> List a -> List a
adjacentUniqueGo previous [] = []
adjacentUniqueGo previous (next :: rest) =
  if previous == next then adjacentUniqueGo previous rest
  else next :: adjacentUniqueGo next rest

adjacentUnique : Eq a => List a -> List a
adjacentUnique [] = []
adjacentUnique (x :: xs) = x :: adjacentUniqueGo x xs

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

public export
observes : (a -> Bool) -> List a -> Bool
observes p [] = False
observes p (x :: xs) = p x || observes p xs

observesUniqueGo : Eq a => (p : a -> Bool) ->
  ((x, y : a) -> x == y = True -> p x = p y) ->
  (previous : a) -> (xs : List a) ->
  (p previous || observes p (adjacentUniqueGo previous xs)) =
  (p previous || observes p xs)
observesUniqueGo p respects previous [] = Refl
observesUniqueGo p respects previous (next :: rest) with (previous == next) proof equal
  observesUniqueGo p respects previous (next :: rest) | True with (p previous) proof value
    observesUniqueGo p respects previous (next :: rest) | True | True = Refl
    observesUniqueGo p respects previous (next :: rest) | True | False =
      rewrite sym (respects previous next equal) in
      rewrite value in
      replace {p = \v => (v || observes p (adjacentUniqueGo previous rest)) = (v || observes p rest)} value (observesUniqueGo p respects previous rest)
  observesUniqueGo p respects previous (next :: rest) | False with (p previous)
    observesUniqueGo p respects previous (next :: rest) | False | True = Refl
    observesUniqueGo p respects previous (next :: rest) | False | False =
      observesUniqueGo p respects next rest

||| Adjacent deduplication preserves any Boolean observation compatible with
||| the actual Eq instance, without assuming the list is sorted.
public export
observesAdjacentUnique : Eq a => (p : a -> Bool) ->
  ((x, y : a) -> x == y = True -> p x = p y) ->
  (xs : List a) -> observes p (adjacentUnique xs) = observes p xs
observesAdjacentUnique p respects [] = Refl
observesAdjacentUnique p respects (x :: xs) = observesUniqueGo p respects x xs

||| The actual adjacent-deduplication pass preserves observations after sort.
||| Consequently, the only remaining canonicalization obligation is sort.
public export
observesCanonicalSorted : Ord a => (p : a -> Bool) ->
  ((x, y : a) -> x == y = True -> p x = p y) ->
  (xs : List a) ->
  observes p (canonicalSorted xs) = observes p (sort xs)
observesCanonicalSorted p respects xs = observesAdjacentUnique p respects (sort xs)
