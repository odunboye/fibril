||| Experimental reduction independent of the opaque library sort.
module Fibril.Foundation.DeMorgan.VerifiedReduction

import Fibril.Foundation.DeMorgan.Sorted
import Fibril.Foundation.DeMorgan.NormalForm

%default total

public export
insertBy : (a -> a -> Ordering) -> a -> List a -> List a
insertBy cmp x [] = [x]
insertBy cmp x (y :: ys) = case cmp x y of
  GT => y :: insertBy cmp x ys
  _ => x :: y :: ys

public export
insertionSortBy : (a -> a -> Ordering) -> List a -> List a
insertionSortBy cmp [] = []
insertionSortBy cmp (x :: xs) = insertBy cmp x (insertionSortBy cmp xs)

swapOr : (a, b, c : Bool) -> a || (b || c) = b || (a || c)
swapOr False False c = Refl
swapOr False True c = Refl
swapOr True False c = Refl
swapOr True True c = Refl

public export
observesInsertBy : (cmp : a -> a -> Ordering) -> (p : a -> Bool) ->
  (x : a) -> (xs : List a) ->
  observes p (insertBy cmp x xs) = (p x || observes p xs)
observesInsertBy cmp p x [] with (p x)
  observesInsertBy cmp p x [] | False = Refl
  observesInsertBy cmp p x [] | True = Refl
observesInsertBy cmp p x (y :: ys) with (cmp x y)
  observesInsertBy cmp p x (y :: ys) | LT = Refl
  observesInsertBy cmp p x (y :: ys) | EQ = Refl
  observesInsertBy cmp p x (y :: ys) | GT =
    trans (cong (p y ||) (observesInsertBy cmp p x ys))
          (sym (swapOr (p x) (p y) (observes p ys)))

public export
observesInsertionSortBy : (cmp : a -> a -> Ordering) -> (p : a -> Bool) ->
  (xs : List a) -> observes p (insertionSortBy cmp xs) = observes p xs
observesInsertionSortBy cmp p [] = Refl
observesInsertionSortBy cmp p (x :: xs) =
  trans (observesInsertBy cmp p x (insertionSortBy cmp xs))
        (cong (p x ||) (observesInsertionSortBy cmp p xs))

public export
verifiedCanonicalSorted : Ord a => List a -> List a
verifiedCanonicalSorted xs = adjacentUnique (insertionSortBy compare xs)

public export
observesVerifiedCanonicalSorted : Ord a => (p : a -> Bool) ->
  ((x, y : a) -> x == y = True -> p x = p y) -> (xs : List a) ->
  observes p (verifiedCanonicalSorted xs) = observes p xs
observesVerifiedCanonicalSorted p respects xs =
  trans (observesAdjacentUnique p respects (insertionSortBy compare xs))
        (observesInsertionSortBy compare p xs)

public export
verifiedReduce : DNF -> DNF
verifiedReduce ds =
  let unique = verifiedCanonicalSorted (map Fibril.Foundation.DeMorgan.VerifiedReduction.verifiedCanonicalSorted ds) in
  filter (\c => not (any (\d => d /= c && subsetSorted d c) unique)) unique

public export
evalVerifiedClause : (env : SignedAssignment) -> (xs : Clause) ->
  evalClause env (verifiedCanonicalSorted xs) = evalClause env xs
evalVerifiedClause env xs =
  trans (evalClauseObserves env (verifiedCanonicalSorted xs)) $
  trans (cong not (observesVerifiedCanonicalSorted (\x => not (evalLiteral env x))
    (\x, y, eq => cong (\z => not (evalLiteral env z)) (literalEqualTrue x y eq)) xs)) $
  sym (evalClauseObserves env xs)

public export
evalVerifiedDNFCanonical : (env : SignedAssignment) -> (ds : DNF) ->
  evalDNF env (verifiedCanonicalSorted ds) = evalDNF env ds
evalVerifiedDNFCanonical env ds =
  trans (evalDNFObserves env (verifiedCanonicalSorted ds)) $
  trans (observesVerifiedCanonicalSorted (evalClause env)
    (\x, y, eq => cong (evalClause env) (clauseEqualTrue x y eq)) ds) $
  sym (evalDNFObserves env ds)

evalMapVerified : (env : SignedAssignment) -> (ds : DNF) ->
  evalDNF env (map Fibril.Foundation.DeMorgan.VerifiedReduction.verifiedCanonicalSorted ds) = evalDNF env ds
evalMapVerified env [] = Refl
evalMapVerified env (x :: xs) =
  rewrite evalVerifiedClause env x in
  rewrite evalMapVerified env xs in Refl

||| Unconditional for independently assigned positive and negative literals.
public export
evalVerifiedReduce : (env : SignedAssignment) -> (ds : DNF) ->
  evalDNF env (verifiedReduce ds) = evalDNF env ds
evalVerifiedReduce env ds =
  trans (evalAbsorptionFilter env (verifiedCanonicalSorted (map Fibril.Foundation.DeMorgan.VerifiedReduction.verifiedCanonicalSorted ds))) $
  trans (evalVerifiedDNFCanonical env (map Fibril.Foundation.DeMorgan.VerifiedReduction.verifiedCanonicalSorted ds)) $
  evalMapVerified env ds
