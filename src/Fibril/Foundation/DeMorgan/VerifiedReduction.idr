||| Experimental reduction independent of the opaque library sort.
module Fibril.Foundation.DeMorgan.VerifiedReduction

import Fibril.Foundation.DeMorgan.Sorted
import Fibril.Foundation.DeMorgan.NormalForm
import Fibril.Foundation.DeMorgan.Interval

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

public export
verifiedJoinDNF : DNF -> DNF -> DNF
verifiedJoinDNF xs ys = verifiedReduce (xs ++ ys)

public export
verifiedMeetDNF : DNF -> DNF -> DNF
verifiedMeetDNF xs ys = verifiedReduce (concatMap (\x => map (\y => x ++ y) ys) xs)

||| Candidate with the same structural recursion as normal, using verifiedReduce.
public export
verifiedNormal : Bool -> Interval Nat -> DNF
verifiedNormal False Zero = []
verifiedNormal True Zero = [[]]
verifiedNormal False One = [[]]
verifiedNormal True One = []
verifiedNormal polarity (Var n) = [[(n, polarity)]]
verifiedNormal polarity (Reverse x) = verifiedNormal (not polarity) x
verifiedNormal False (Meet x y) = verifiedMeetDNF (verifiedNormal False x) (verifiedNormal False y)
verifiedNormal True (Meet x y) = verifiedJoinDNF (verifiedNormal True x) (verifiedNormal True y)
verifiedNormal False (Join x y) = verifiedJoinDNF (verifiedNormal False x) (verifiedNormal False y)
verifiedNormal True (Join x y) = verifiedMeetDNF (verifiedNormal True x) (verifiedNormal True y)

public export
evalVerifiedJoinDNF : (env : SignedAssignment) -> (xs, ys : DNF) ->
  evalDNF env (verifiedJoinDNF xs ys) = (evalDNF env xs || evalDNF env ys)
evalVerifiedJoinDNF env xs ys = trans (evalVerifiedReduce env (xs ++ ys)) (evalDNFAppend env xs ys)

public export
evalVerifiedMeetDNF : (env : SignedAssignment) -> (xs, ys : DNF) ->
  evalDNF env (verifiedMeetDNF xs ys) = (evalDNF env xs && evalDNF env ys)
evalVerifiedMeetDNF env xs ys =
  trans (evalVerifiedReduce env (concatMap (\x => map (\y => x ++ y) ys) xs)) (evalMeetProduct env xs ys)

||| Unconditional signed evaluation preservation for the candidate normalizer.
public export
evalVerifiedNormal : (env : SignedAssignment) -> (polarity : Bool) -> (x : Interval Nat) ->
  evalDNF env (verifiedNormal polarity x) = evalSigned env polarity x
evalVerifiedNormal env False Zero = Refl
evalVerifiedNormal env True Zero = Refl
evalVerifiedNormal env False One = Refl
evalVerifiedNormal env True One = Refl
evalVerifiedNormal env False (Var n) with (env n False)
  evalVerifiedNormal env False (Var n) | False = Refl
  evalVerifiedNormal env False (Var n) | True = Refl
evalVerifiedNormal env True (Var n) with (env n True)
  evalVerifiedNormal env True (Var n) | False = Refl
  evalVerifiedNormal env True (Var n) | True = Refl
evalVerifiedNormal env False (Reverse x) = evalVerifiedNormal env True x
evalVerifiedNormal env True (Reverse x) = evalVerifiedNormal env False x
evalVerifiedNormal env False (Meet x y) =
  rewrite evalVerifiedMeetDNF env (verifiedNormal False x) (verifiedNormal False y) in
  rewrite evalVerifiedNormal env False x in
  rewrite evalVerifiedNormal env False y in Refl
evalVerifiedNormal env True (Meet x y) =
  rewrite evalVerifiedJoinDNF env (verifiedNormal True x) (verifiedNormal True y) in
  rewrite evalVerifiedNormal env True x in
  rewrite evalVerifiedNormal env True y in Refl
evalVerifiedNormal env False (Join x y) =
  rewrite evalVerifiedJoinDNF env (verifiedNormal False x) (verifiedNormal False y) in
  rewrite evalVerifiedNormal env False x in
  rewrite evalVerifiedNormal env False y in Refl
evalVerifiedNormal env True (Join x y) =
  rewrite evalVerifiedMeetDNF env (verifiedNormal True x) (verifiedNormal True y) in
  rewrite evalVerifiedNormal env True x in
  rewrite evalVerifiedNormal env True y in Refl
