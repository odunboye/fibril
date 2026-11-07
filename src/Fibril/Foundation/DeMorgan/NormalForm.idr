-- Reference free De Morgan algebra equality via absorbed DNF. Exponential
-- growth is possible. No Boolean complement laws or face rules apply here.
-- Theory: CCHM18 specifies the algebra; reduction soundness remains unproved.
-- Bibliography and limitations: docs/references.md.
module Fibril.Foundation.DeMorgan.NormalForm

import Data.List
import Data.List.Elem
import Data.Nat

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

-- A clause can be removed from a disjunction when the rest already implies it
-- in the absorption direction: whenever the clause holds, the rest holds.
public export
evalDNFAbsorb : (env : SignedAssignment) -> (before, after : DNF) ->
  (clause : Clause) ->
  (evalClause env clause = True -> evalDNF env (before ++ after) = True) ->
  evalDNF env (before ++ clause :: after) = evalDNF env (before ++ after)
evalDNFAbsorb env [] after clause absorbed with (evalClause env clause) proof eq
  evalDNFAbsorb env [] after clause absorbed | False = Refl
  evalDNFAbsorb env [] after clause absorbed | True = sym (absorbed Refl)
evalDNFAbsorb env (x :: xs) after clause absorbed with (evalClause env x) proof eq
  evalDNFAbsorb env (x :: xs) after clause absorbed | True = Refl
  evalDNFAbsorb env (x :: xs) after clause absorbed | False =
    evalDNFAbsorb env xs after clause (\holds => absorbed holds)

||| Soundness of the actual merge-style subset check, without a sortedness
||| assumption. The comparison compatibility premise is needed only at EQ.
public export
subsetSortedHolds : (env : SignedAssignment) ->
  ((x, y : Literal) -> compare x y = EQ -> evalLiteral env x = evalLiteral env y) ->
  (xs, ys : Clause) -> subsetSorted xs ys = True ->
  evalClause env ys = True -> evalClause env xs = True
subsetSortedHolds env compatible [] ys subset holds = Refl
subsetSortedHolds env compatible (x :: xs) [] subset holds impossible
subsetSortedHolds env compatible (x :: xs) (y :: ys) subset holds with (compare x y) proof order
  subsetSortedHolds env compatible (x :: xs) (y :: ys) subset holds | LT impossible
  subsetSortedHolds env compatible (x :: xs) (y :: ys) subset holds | EQ with (evalLiteral env y) proof value
    subsetSortedHolds env compatible (x :: xs) (y :: ys) subset holds | EQ | False impossible
    subsetSortedHolds env compatible (x :: xs) (y :: ys) subset holds | EQ | True =
      rewrite compatible x y order in
      rewrite value in
      subsetSortedHolds env compatible xs ys subset holds
  subsetSortedHolds env compatible (x :: xs) (y :: ys) subset holds | GT with (evalLiteral env y)
    subsetSortedHolds env compatible (x :: xs) (y :: ys) subset holds | GT | False impossible
    subsetSortedHolds env compatible (x :: xs) (y :: ys) subset holds | GT | True =
      subsetSortedHolds env compatible (x :: xs) ys subset holds

natEqualTrue : (x, y : Nat) -> (x == y) = True -> x = y
natEqualTrue Z Z eq = Refl
natEqualTrue Z (S y) eq impossible
natEqualTrue (S x) Z eq impossible
natEqualTrue (S x) (S y) eq = cong S (natEqualTrue x y eq)

natCompareEqBool : (x, y : Nat) -> compare x y = EQ -> (x == y) = True
natCompareEqBool Z Z eq = Refl
natCompareEqBool Z (S y) eq impossible
natCompareEqBool (S x) Z eq impossible
natCompareEqBool (S x) (S y) eq = natCompareEqBool x y eq

literalCompareEqual : (x, y : Literal) -> compare x y = EQ -> x = y
literalCompareEqual (x, a) (y, b) eq with (x == y) proof same
  literalCompareEqual (x, a) (y, b) eq | False =
    absurd (trans (sym same) (natCompareEqBool x y eq))
  literalCompareEqual (x, False) (y, False) eq | True =
    cong (\n => (n, False)) (natEqualTrue x y same)
  literalCompareEqual (x, False) (y, True) eq | True impossible
  literalCompareEqual (x, True) (y, False) eq | True impossible
  literalCompareEqual (x, True) (y, True) eq | True =
    cong (\n => (n, True)) (natEqualTrue x y same)

||| A successful actual subsetSorted check implies semantic absorption,
||| even on unsorted inputs (sortedness is needed for completeness only).
public export
subsetSortedClauseHolds : (env : SignedAssignment) -> (xs, ys : Clause) ->
  subsetSorted xs ys = True -> evalClause env ys = True -> evalClause env xs = True
subsetSortedClauseHolds env xs ys = subsetSortedHolds env
  (\x, y, eq => cong (evalLiteral env) (literalCompareEqual x y eq)) xs ys

boolEqualTrue : (x, y : Bool) -> (x == y) = True -> x = y
boolEqualTrue False False eq = Refl
boolEqualTrue False True eq impossible
boolEqualTrue True False eq impossible
boolEqualTrue True True eq = Refl

public export
literalEqualTrue : (x, y : Literal) -> (x == y) = True -> x = y
literalEqualTrue (n, a) (m, b) eq with (n == m) proof names
  literalEqualTrue (n, a) (m, b) eq | False impossible
  literalEqualTrue (n, a) (m, b) eq | True =
    cong2 (,) (natEqualTrue n m names) (boolEqualTrue a b eq)

public export
clauseEqualTrue : (xs, ys : Clause) -> (xs == ys) = True -> xs = ys
clauseEqualTrue [] [] eq = Refl
clauseEqualTrue [] (y :: ys) eq impossible
clauseEqualTrue (x :: xs) [] eq impossible
clauseEqualTrue (x :: xs) (y :: ys) eq with (x == y) proof headEq
  clauseEqualTrue (x :: xs) (y :: ys) eq | False impossible
  clauseEqualTrue (x :: xs) (y :: ys) eq | True =
    cong2 (::) (literalEqualTrue x y headEq) (clauseEqualTrue xs ys eq)

public export
evalDNFObserves : (env : SignedAssignment) -> (ds : DNF) ->
  evalDNF env ds = observes (evalClause env) ds
evalDNFObserves env [] = Refl
evalDNFObserves env (x :: xs) = cong (evalClause env x ||) (evalDNFObserves env xs)

||| The actual outer canonicalization's dedup pass preserves DNF evaluation.
||| This isolates sort preservation as the only remaining outer obligation.
public export
evalDNFCanonicalSorted : (env : SignedAssignment) -> (ds : DNF) ->
  evalDNF env (canonicalSorted ds) = evalDNF env (sort ds)
evalDNFCanonicalSorted env ds =
  trans (evalDNFObserves env (canonicalSorted ds)) $
  trans (observesCanonicalSorted (evalClause env)
    (\x, y, eq => cong (evalClause env) (clauseEqualTrue x y eq)) ds) $
  sym (evalDNFObserves env (sort ds))

public export
evalClauseObserves : (env : SignedAssignment) -> (xs : Clause) ->
  evalClause env xs = not (observes (\x => not (evalLiteral env x)) xs)
evalClauseObserves env [] = Refl
evalClauseObserves env (x :: xs) with (evalLiteral env x)
  evalClauseObserves env (x :: xs) | False = Refl
  evalClauseObserves env (x :: xs) | True = evalClauseObserves env xs

||| The actual literal canonicalization's dedup pass preserves clause evaluation.
public export
evalClauseCanonicalSorted : (env : SignedAssignment) -> (xs : Clause) ->
  evalClause env (canonicalSorted xs) = evalClause env (sort xs)
evalClauseCanonicalSorted env xs =
  trans (evalClauseObserves env (canonicalSorted xs)) $
  trans (cong not (observesCanonicalSorted (\x => not (evalLiteral env x))
    (\x, y, eq => cong (\z => not (evalLiteral env z)) (literalEqualTrue x y eq)) xs)) $
  sym (evalClauseObserves env (sort xs))

evalDNFMember : (env : SignedAssignment) -> (ds : DNF) ->
  (c : Clause) -> Elem c ds -> evalClause env c = True -> evalDNF env ds = True
evalDNFMember env (c :: ds) c Here holds = rewrite holds in Refl
evalDNFMember env (x :: ds) c (There member) holds with (evalClause env x)
  evalDNFMember env (x :: ds) c (There member) holds | True = Refl
  evalDNFMember env (x :: ds) c (There member) holds | False =
    evalDNFMember env ds c member holds

evalDNFWitness : (env : SignedAssignment) -> (ds : DNF) ->
  evalDNF env ds = True -> (c : Clause ** (Elem c ds, evalClause env c = True))
evalDNFWitness env [] holds impossible
evalDNFWitness env (x :: xs) holds with (evalClause env x) proof value
  evalDNFWitness env (x :: xs) holds | True = (x ** (Here, value))
  evalDNFWitness env (x :: xs) holds | False =
    let (c ** (member, trueClause)) = evalDNFWitness env xs holds in
      (c ** (There member, trueClause))

filterMemberOriginal : (keep : a -> Bool) -> (xs : List a) ->
  Elem x (filter keep xs) -> Elem x xs
filterMemberOriginal keep [] member impossible
filterMemberOriginal keep (y :: ys) member with (keep y)
  filterMemberOriginal keep (y :: ys) Here | True = Here
  filterMemberOriginal keep (y :: ys) (There later) | True =
    There (filterMemberOriginal keep ys later)
  filterMemberOriginal keep (y :: ys) member | False =
    There (filterMemberOriginal keep ys member)

filterMemberKept : (keep : a -> Bool) -> (xs : List a) ->
  Elem x xs -> keep x = True -> Elem x (filter keep xs)
filterMemberKept keep (x :: xs) Here holds = rewrite holds in Here
filterMemberKept keep (y :: ys) (There later) holds with (keep y)
  filterMemberKept keep (y :: ys) (There later) holds | True =
    There (filterMemberKept keep ys later holds)
  filterMemberKept keep (y :: ys) (There later) holds | False =
    filterMemberKept keep ys later holds

filterSurvivingTrue : (env : SignedAssignment) -> (keep : Clause -> Bool) ->
  (ds : DNF) ->
  ((c : Clause) -> Elem c ds -> keep c = False -> evalClause env c = True ->
    evalDNF env (filter keep ds) = True) ->
  (c : Clause) -> Elem c ds -> evalClause env c = True ->
  evalDNF env (filter keep ds) = True
filterSurvivingTrue env keep ds survives c member holds with (keep c) proof kept
  filterSurvivingTrue env keep ds survives c member holds | True =
    evalDNFMember env (filter keep ds) c (filterMemberKept keep ds member kept) holds
  filterSurvivingTrue env keep ds survives c member holds | False =
    survives c member kept holds

||| Filtering preserves DNF evaluation if each removed true clause has some
||| true surviving clause. The witness may occur anywhere in the original list.
public export
evalDNFFilterIfSurvives : (env : SignedAssignment) -> (keep : Clause -> Bool) ->
  (ds : DNF) ->
  ((c : Clause) -> Elem c ds -> keep c = False -> evalClause env c = True ->
    evalDNF env (filter keep ds) = True) ->
  evalDNF env (filter keep ds) = evalDNF env ds
evalDNFFilterIfSurvives env keep ds survives with (evalDNF env ds) proof original
  evalDNFFilterIfSurvives env keep ds survives | False with (evalDNF env (filter keep ds)) proof filtered
    evalDNFFilterIfSurvives env keep ds survives | False | False = Refl
    evalDNFFilterIfSurvives env keep ds survives | False | True =
      let (c ** (member, holds)) = evalDNFWitness env (filter keep ds) filtered
          originalTrue = evalDNFMember env ds c (filterMemberOriginal keep ds member) holds
       in absurd (trans (sym original) originalTrue)
  evalDNFFilterIfSurvives env keep ds survives | True =
    let (c ** (member, holds)) = evalDNFWitness env ds original in
    filterSurvivingTrue env keep ds survives c member holds

||| Exact filter used by reduce: it suffices to find, for every removed
||| true clause, a retained subset in the original input list.
public export
evalAbsorptionFilterIfSurvivors : (env : SignedAssignment) -> (ds : DNF) ->
  ((c : Clause) -> Elem c ds ->
    not (any (\d => d /= c && subsetSorted d c) ds) = False ->
    evalClause env c = True ->
    (d : Clause ** (Elem d ds,
      not (any (\e => e /= d && subsetSorted e d) ds) = True,
      subsetSorted d c = True))) ->
  evalDNF env (filter (\c => not (any (\d => d /= c && subsetSorted d c) ds)) ds) =
  evalDNF env ds
evalAbsorptionFilterIfSurvivors env ds survivors =
  evalDNFFilterIfSurvives env
    (\c => not (any (\d => d /= c && subsetSorted d c) ds)) ds $
    \c, member, removed, holds =>
      let (d ** (inOriginal, retained, subset)) = survivors c member removed holds in
      evalDNFMember env _ d (filterMemberKept _ ds inOriginal retained)
        (subsetSortedClauseHolds env d c subset holds)

foldAnyTrue : (p : a -> Bool) -> (xs : List a) ->
  foldl (\acc, x => acc || p x) True xs = True
foldAnyTrue p [] = Refl
foldAnyTrue p (x :: xs) = foldAnyTrue p xs

foldAnyObserves : (p : a -> Bool) -> (xs : List a) ->
  foldl (\acc, x => acc || p x) False xs = observes p xs
foldAnyObserves p [] = Refl
foldAnyObserves p (x :: xs) with (p x)
  foldAnyObserves p (x :: xs) | False = foldAnyObserves p xs
  foldAnyObserves p (x :: xs) | True = foldAnyTrue p xs

anyObserves : (p : a -> Bool) -> (xs : List a) -> any p xs = observes p xs
anyObserves p xs = foldAnyObserves p xs

observesWitness : (p : a -> Bool) -> (xs : List a) -> observes p xs = True ->
  (x : a ** (Elem x xs, p x = True))
observesWitness p [] holds impossible
observesWitness p (x :: xs) holds with (p x) proof value
  observesWitness p (x :: xs) holds | True = (x ** (Here, value))
  observesWitness p (x :: xs) holds | False =
    let (y ** (member, yes)) = observesWitness p xs holds in
    (y ** (There member, yes))

||| Every clause removed by the actual absorption predicate has a distinct
||| subset witness in the same original input list (not necessarily retained).
public export
absorptionRemovedWitness : (ds : DNF) -> (c : Clause) ->
  not (any (\d => d /= c && subsetSorted d c) ds) = False ->
  (d : Clause ** (Elem d ds, d /= c = True, subsetSorted d c = True))
absorptionRemovedWitness ds c removed =
  let check : Clause -> Bool
      check = \d => d /= c && subsetSorted d c
      observed : observes check ds = True
      observed = trans (sym (anyObserves check ds)) (notFalseTrue _ removed)
   in let (d ** (member, matches)) = observesWitness check ds observed
       in (d ** (member, fst (andTrue _ _ matches), snd (andTrue _ _ matches)))
  where
    notFalseTrue : (b : Bool) -> not b = False -> b = True
    notFalseTrue False eq impossible
    notFalseTrue True eq = Refl
    andTrue : (a, b : Bool) -> a && b = True -> (a = True, b = True)
    andTrue False b eq impossible
    andTrue True b eq = (Refl, eq)

||| A successful merge check never increases clause length, even if unsorted.
public export
subsetSortedLength : (xs, ys : Clause) -> subsetSorted xs ys = True -> LTE (length xs) (length ys)
subsetSortedLength [] ys ok = LTEZero
subsetSortedLength (x :: xs) [] ok impossible
subsetSortedLength (x :: xs) (y :: ys) ok with (compare x y)
  subsetSortedLength (x :: xs) (y :: ys) ok | LT impossible
  subsetSortedLength (x :: xs) (y :: ys) ok | EQ = LTESucc (subsetSortedLength xs ys ok)
  subsetSortedLength (x :: xs) (y :: ys) ok | GT = lteSuccRight (subsetSortedLength (x :: xs) ys ok)

||| Equal-length successful checks identify the actual literal lists.
public export
subsetSortedEqualLength : (xs, ys : Clause) -> subsetSorted xs ys = True -> length xs = length ys -> xs = ys
subsetSortedEqualLength [] [] ok len = Refl
subsetSortedEqualLength [] (y :: ys) ok len impossible
subsetSortedEqualLength (x :: xs) [] ok len impossible
subsetSortedEqualLength (x :: xs) (y :: ys) ok len with (compare x y) proof order
  subsetSortedEqualLength (x :: xs) (y :: ys) ok len | LT impossible
  subsetSortedEqualLength (x :: xs) (y :: ys) ok len | EQ =
    cong2 (::) (literalCompareEqual x y order) (subsetSortedEqualLength xs ys ok (injective len))
  subsetSortedEqualLength (x :: xs) (y :: ys) ok len | GT =
    let bound : LTE (S (length xs)) (length xs)
        bound = replace {p = \n => LTE (S (length xs)) n} (sym (injective len)) (subsetSortedLength (x :: xs) ys ok)
     in absurd (succNotLTEpred bound)

natEqSelf : (n : Nat) -> (n == n) = True
natEqSelf Z = Refl
natEqSelf (S n) = natEqSelf n

literalEqSelf : (x : Literal) -> (x == x) = True
literalEqSelf (n, False) = rewrite natEqSelf n in Refl
literalEqSelf (n, True) = rewrite natEqSelf n in Refl

clauseEqSelf : (xs : Clause) -> (xs == xs) = True
clauseEqSelf [] = Refl
clauseEqSelf (x :: xs) = rewrite literalEqSelf x in clauseEqSelf xs

strictFromLTE : (n, m : Nat) -> LTE n m -> Not (n = m) -> LTE (S n) m
strictFromLTE Z Z bound neq = absurd (neq Refl)
strictFromLTE Z (S m) bound neq = LTESucc LTEZero
strictFromLTE (S n) (S m) (LTESucc bound) neq =
  LTESucc (strictFromLTE n m bound (\eq => neq (cong S eq)))

||| Distinct successful absorbers are strictly shorter, ruling out cycles.
public export
subsetSortedStrictLength : (xs, ys : Clause) -> xs /= ys = True ->
  subsetSorted xs ys = True -> LTE (S (length xs)) (length ys)
subsetSortedStrictLength xs ys distinct subset =
  strictFromLTE (length xs) (length ys) (subsetSortedLength xs ys subset) $
    \same => let equal = subsetSortedEqualLength xs ys subset same in
      replace {p = \zs => zs /= ys = True -> Void} (sym equal)
        (\bad => absurd (trans (sym (clauseEqSelf ys)) (notTrueFalse (ys == ys) bad))) distinct
  where
    notTrueFalse : (b : Bool) -> (not b = True) -> b = False
    notTrueFalse False p = Refl
    notTrueFalse True p impossible

absorptionSurvivesFuel : (fuel : Nat) -> (env : SignedAssignment) -> (ds : DNF) ->
  (c : Clause) -> LTE (S (length c)) fuel -> Elem c ds -> evalClause env c = True ->
  evalDNF env (filter (\x => not (any (\d => d /= x && subsetSorted d x) ds)) ds) = True
absorptionSurvivesFuel Z env ds c bound member holds impossible
absorptionSurvivesFuel (S fuel) env ds c (LTESucc bound) member holds with
  (not (any (\d => d /= c && subsetSorted d c) ds)) proof kept
  absorptionSurvivesFuel (S fuel) env ds c (LTESucc bound) member holds | True =
    evalDNFMember env _ c (filterMemberKept _ ds member kept) holds
  absorptionSurvivesFuel (S fuel) env ds c (LTESucc bound) member holds | False =
    let (d ** (inOriginal, distinct, subset)) = absorptionRemovedWitness ds c kept in
    absorptionSurvivesFuel fuel env ds d
      (transitive (subsetSortedStrictLength d c distinct subset) bound)
      inOriginal (subsetSortedClauseHolds env d c subset holds)

||| The exact absorption filter preserves evaluation for every DNF, including
||| unsorted and duplicate clauses; no transitivity of subsetSorted is needed.
public export
evalAbsorptionFilter : (env : SignedAssignment) -> (ds : DNF) ->
  evalDNF env (filter (\c => not (any (\d => d /= c && subsetSorted d c) ds)) ds) =
  evalDNF env ds
evalAbsorptionFilter env ds =
  evalDNFFilterIfSurvives env _ ds $ \c, member, removed, holds =>
    absorptionSurvivesFuel (S (length c)) env ds c (LTESucc reflexive) member holds

evalDNFMapCanonical : (env : SignedAssignment) ->
  ((xs : Clause) -> evalClause env (sort xs) = evalClause env xs) ->
  (ds : DNF) -> evalDNF env (map Fibril.Foundation.DeMorgan.Sorted.canonicalSorted ds) = evalDNF env ds
evalDNFMapCanonical env sortSound [] = Refl
evalDNFMapCanonical env sortSound (x :: xs) =
  rewrite evalClauseCanonicalSorted env x in
  rewrite sortSound x in
  rewrite evalDNFMapCanonical env sortSound xs in Refl

||| The canonicalized clause list consumed by the absorption filter.
public export
preAbsorption : DNF -> DNF
preAbsorption ds = canonicalSorted (map canonicalSorted ds)

||| Earlier stronger conditional form, retained for callers that already have
||| direct surviving subset witnesses. See reductionSoundIfSort below.
public export
reductionSoundIfSortAndSurvivors : (env : SignedAssignment) ->
  ((xs : Clause) -> evalClause env (sort xs) = evalClause env xs) ->
  ((ds : DNF) -> evalDNF env (sort ds) = evalDNF env ds) ->
  ((ds : DNF) ->
    (c : Clause) -> Elem c (preAbsorption ds) ->
    not (any (\d => d /= c && subsetSorted d c) (preAbsorption ds)) = False ->
    evalClause env c = True ->
    (d : Clause ** (Elem d (preAbsorption ds),
      not (any (\e => e /= d && subsetSorted e d) (preAbsorption ds)) = True,
      subsetSorted d c = True))) ->
  ReductionSound env
reductionSoundIfSortAndSurvivors env literalSort clauseSort survivors ds =
  trans (evalAbsorptionFilterIfSurvivors env
    (canonicalSorted (map canonicalSorted ds))
    (survivors ds)) $
  trans (evalDNFCanonicalSorted env (map canonicalSorted ds)) $
  trans (clauseSort (map canonicalSorted ds)) $
  evalDNFMapCanonical env literalSort ds

||| Actual reduction is sound provided the two library sorts preserve evaluation.
public export
reductionSoundIfSort : (env : SignedAssignment) ->
  ((xs : Clause) -> evalClause env (sort xs) = evalClause env xs) ->
  ((ds : DNF) -> evalDNF env (sort ds) = evalDNF env ds) ->
  ReductionSound env
reductionSoundIfSort env literalSort clauseSort ds =
  trans (evalAbsorptionFilter env (preAbsorption ds)) $
  trans (evalDNFCanonicalSorted env (map canonicalSorted ds)) $
  trans (clauseSort (map canonicalSorted ds)) $
  evalDNFMapCanonical env literalSort ds
