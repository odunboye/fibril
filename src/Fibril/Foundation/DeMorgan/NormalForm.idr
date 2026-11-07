-- Reference free De Morgan algebra equality via absorbed DNF. Exponential
-- growth is possible. No Boolean complement laws or face rules apply here.
-- Theory: CCHM18 specifies the algebra; reduction soundness remains unproved.
-- Bibliography and limitations: docs/references.md.
module Fibril.Foundation.DeMorgan.NormalForm

import Data.List
import Fibril.Foundation.DeMorgan.Sorted
import Fibril.Foundation.DeMorgan.Interval

%default total

-- A join of meets of signed generators. Complementary literals are NOT
-- cancelled: the interval is De Morgan, not Boolean.
public export
Literal : Type
Literal = (Nat, Bool)

public export
Clause : Type
Clause = List Literal

public export
DNF : Type
DNF = List Clause

canonical : Ord a => List a -> List a
canonical = canonicalSorted

subset : Clause -> Clause -> Bool
subset = subsetSorted

public export
reduce : DNF -> DNF
reduce clauses =
  let unique = canonical (map canonical clauses)
   in filter (\c => not (any (\d => d /= c && subset d c) unique)) unique

public export
joinDNF : DNF -> DNF -> DNF
joinDNF xs ys = reduce (xs ++ ys)

public export
meetDNF : DNF -> DNF -> DNF
meetDNF xs ys = reduce (concatMap (\x => map (\y => x ++ y) ys) xs)

-- Push reversal to generators structurally; polarity avoids a separate
-- non-structural rewrite pass.
public export
normal : Bool -> Interval Nat -> DNF
normal False Zero = []
normal True Zero = [[]]
normal False One = [[]]
normal True One = []
normal polarity (Var n) = [[(n, polarity)]]
normal polarity (Reverse x) = normal (not polarity) x
normal False (Meet x y) = meetDNF (normal False x) (normal False y)
normal True (Meet x y) = joinDNF (normal True x) (normal True y)
normal False (Join x y) = joinDNF (normal False x) (normal False y)
normal True (Join x y) = meetDNF (normal True x) (normal True y)

||| Symbolic equality in the free De Morgan algebra on Nat-labelled generators.
||| Exponential normal-form growth is possible; this is a reference algorithm.
public export
equivalent : Interval Nat -> Interval Nat -> Bool
equivalent x y = normal False x == normal False y

-- Independent values for the positive and negative occurrence of each name.
public export
SignedAssignment : Type
SignedAssignment = Nat -> Bool -> Bool

public export
evalLiteral : SignedAssignment -> Literal -> Bool
evalLiteral env (name, polarity) = env name polarity

public export
evalClause : SignedAssignment -> Clause -> Bool
evalClause env [] = True
evalClause env (x :: xs) = evalLiteral env x && evalClause env xs

public export
evalDNF : SignedAssignment -> DNF -> Bool
evalDNF env [] = False
evalDNF env (x :: xs) = evalClause env x || evalDNF env xs

andAssoc : (a, b, c : Bool) -> a && (b && c) = (a && b) && c
andAssoc False b c = Refl
andAssoc True b c = Refl

orAssoc : (a, b, c : Bool) -> a || (b || c) = (a || b) || c
orAssoc False b c = Refl
orAssoc True b c = Refl

andOrDistrib : (a, b, c : Bool) -> (a && b) || (a && c) = a && (b || c)
andOrDistrib False b c = Refl
andOrDistrib True b c = Refl

public export
evalClauseAppend : (env : SignedAssignment) -> (xs, ys : Clause) ->
  evalClause env (xs ++ ys) = (evalClause env xs && evalClause env ys)
evalClauseAppend env [] ys = Refl
evalClauseAppend env (x :: xs) ys =
  rewrite evalClauseAppend env xs ys in
  andAssoc (evalLiteral env x) (evalClause env xs) (evalClause env ys)

public export
evalDNFAppend : (env : SignedAssignment) -> (xs, ys : DNF) ->
  evalDNF env (xs ++ ys) = (evalDNF env xs || evalDNF env ys)
evalDNFAppend env [] ys = Refl
evalDNFAppend env (x :: xs) ys =
  rewrite evalDNFAppend env xs ys in
  orAssoc (evalClause env x) (evalDNF env xs) (evalDNF env ys)

public export
evalMeetRow : (env : SignedAssignment) -> (x : Clause) -> (ys : DNF) ->
  evalDNF env (map (\y => x ++ y) ys) = (evalClause env x && evalDNF env ys)
evalMeetRow env x [] with (evalClause env x)
  evalMeetRow env x [] | False = Refl
  evalMeetRow env x [] | True = Refl
evalMeetRow env x (y :: ys) =
  rewrite evalClauseAppend env x y in
  rewrite evalMeetRow env x ys in
  andOrDistrib (evalClause env x) (evalClause env y) (evalDNF env ys)

productStep : (a, b, c, d : Bool) ->
  (a || (b && d)) || (c && d) = a || ((b || c) && d)
productStep False False c d = Refl
productStep False True False False = Refl
productStep False True True False = Refl
productStep False True c True = Refl
productStep True b c d = Refl

productBase : (a : Bool) -> a = a || False
productBase False = Refl
productBase True = Refl

productFold : (env : SignedAssignment) -> (ys : DNF) -> (xs, acc : DNF) ->
  evalDNF env (foldl (\a, x => a ++ map (\y => x ++ y) ys) acc xs) =
    (evalDNF env acc || (evalDNF env xs && evalDNF env ys))
productFold env ys [] acc = productBase (evalDNF env acc)
productFold env ys (x :: xs) acc =
  rewrite productFold env ys xs (acc ++ map (\y => x ++ y) ys) in
  rewrite evalDNFAppend env acc (map (\y => x ++ y) ys) in
  rewrite evalMeetRow env x ys in
  productStep (evalDNF env acc) (evalClause env x) (evalDNF env xs) (evalDNF env ys)

||| Semantics of the exact Cartesian-product expression used by meetDNF,
||| before its final reduction.
public export
evalMeetProduct : (env : SignedAssignment) -> (xs, ys : DNF) ->
  evalDNF env (concatMap (\x => map (\y => x ++ y) ys) xs) =
    (evalDNF env xs && evalDNF env ys)
evalMeetProduct env xs ys = productFold env ys xs []

||| Reduction preservation is the remaining obligation for these operations.
public export
ReductionSound : SignedAssignment -> Type
ReductionSound env = (ds : DNF) -> evalDNF env (reduce ds) = evalDNF env ds

public export
evalJoinDNF : (env : SignedAssignment) -> ReductionSound env -> (xs, ys : DNF) ->
  evalDNF env (joinDNF xs ys) = (evalDNF env xs || evalDNF env ys)
evalJoinDNF env sound xs ys = trans (sound (xs ++ ys)) (evalDNFAppend env xs ys)

public export
evalMeetDNF : (env : SignedAssignment) -> ReductionSound env -> (xs, ys : DNF) ->
  evalDNF env (meetDNF xs ys) = (evalDNF env xs && evalDNF env ys)
evalMeetDNF env sound xs ys =
  trans (sound (concatMap (\x => map (\y => x ++ y) ys) xs)) (evalMeetProduct env xs ys)

public export
normalReverse : (polarity : Bool) -> (x : Interval Nat) ->
  normal polarity (Reverse x) = normal (not polarity) x
normalReverse False x = Refl
normalReverse True x = Refl

||| Positive and negative occurrences are evaluated independently.
public export
evalSigned : SignedAssignment -> Bool -> Interval Nat -> Bool
evalSigned env False Zero = False
evalSigned env True Zero = True
evalSigned env False One = True
evalSigned env True One = False
evalSigned env polarity (Var n) = env n polarity
evalSigned env polarity (Reverse x) = evalSigned env (not polarity) x
evalSigned env False (Meet x y) = evalSigned env False x && evalSigned env False y
evalSigned env True (Meet x y) = evalSigned env True x || evalSigned env True y
evalSigned env False (Join x y) = evalSigned env False x || evalSigned env False y
evalSigned env True (Join x y) = evalSigned env True x && evalSigned env True y

||| Full structural bridge, conditional only on preservation by actual reduce.
public export
normalSoundIfReduce : (env : SignedAssignment) -> ReductionSound env ->
  (polarity : Bool) -> (x : Interval Nat) ->
  evalDNF env (normal polarity x) = evalSigned env polarity x
normalSoundIfReduce env sound False Zero = Refl
normalSoundIfReduce env sound True Zero = Refl
normalSoundIfReduce env sound False One = Refl
normalSoundIfReduce env sound True One = Refl
normalSoundIfReduce env sound False (Var n) with (env n False)
  normalSoundIfReduce env sound False (Var n) | False = Refl
  normalSoundIfReduce env sound False (Var n) | True = Refl
normalSoundIfReduce env sound True (Var n) with (env n True)
  normalSoundIfReduce env sound True (Var n) | False = Refl
  normalSoundIfReduce env sound True (Var n) | True = Refl
normalSoundIfReduce env sound False (Reverse x) = normalSoundIfReduce env sound True x
normalSoundIfReduce env sound True (Reverse x) = normalSoundIfReduce env sound False x
normalSoundIfReduce env sound False (Meet x y) =
  rewrite evalMeetDNF env sound (normal False x) (normal False y) in
  rewrite normalSoundIfReduce env sound False x in
  rewrite normalSoundIfReduce env sound False y in Refl
normalSoundIfReduce env sound True (Meet x y) =
  rewrite evalJoinDNF env sound (normal True x) (normal True y) in
  rewrite normalSoundIfReduce env sound True x in
  rewrite normalSoundIfReduce env sound True y in Refl
normalSoundIfReduce env sound False (Join x y) =
  rewrite evalJoinDNF env sound (normal False x) (normal False y) in
  rewrite normalSoundIfReduce env sound False x in
  rewrite normalSoundIfReduce env sound False y in Refl
normalSoundIfReduce env sound True (Join x y) =
  rewrite evalMeetDNF env sound (normal True x) (normal True y) in
  rewrite normalSoundIfReduce env sound True x in
  rewrite normalSoundIfReduce env sound True y in Refl
