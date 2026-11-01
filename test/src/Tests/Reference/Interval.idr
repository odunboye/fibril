-- Frozen pre-optimization oracle; keep independent of production clause helpers.
-- Reference free De Morgan algebra equality via absorbed DNF. Exponential
-- growth is possible. No Boolean complement laws or face rules apply here.
-- Theory: CCHM18 specifies the algebra; absorbed DNF is our unverified algorithm choice.
-- Bibliography and limitations: docs/references.md.
module Tests.Reference.Interval

import Data.List
import Fibril.Foundation.DeMorgan.Interval

%default total

-- A join of meets of signed generators. Complementary literals are NOT
-- cancelled: the interval is De Morgan, not Boolean.
Literal : Type
Literal = (Nat, Bool)

Clause : Type
Clause = List Literal

DNF : Type
DNF = List Clause

canonical : Ord a => List a -> List a
canonical = nub . sort

subset : Clause -> Clause -> Bool
subset xs ys = all (\x => elem x ys) xs

reduce : DNF -> DNF
reduce clauses =
  let unique = canonical (map canonical clauses)
   in filter (\c => not (any (\d => d /= c && subset d c) unique)) unique

joinDNF : DNF -> DNF -> DNF
joinDNF xs ys = reduce (xs ++ ys)

meetDNF : DNF -> DNF -> DNF
meetDNF xs ys = reduce (concatMap (\x => map (\y => x ++ y) ys) xs)

-- Push reversal to generators structurally; polarity avoids a separate
-- non-structural rewrite pass.
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
referenceEquivalent : Interval Nat -> Interval Nat -> Bool
referenceEquivalent x y = normal False x == normal False y
