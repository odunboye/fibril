-- Frozen pre-optimization oracle; no production solver/helper calls.
module Tests.Reference.Face

import Data.List
import Fibril.Foundation.DeMorgan.Face

%default total

Atom : Type
Atom = (Nat, Bool)

Clause : Type
Clause = List Atom

DNF : Type
DNF = List Clause

canonical : Ord a => List a -> List a
canonical = nub . sort

subset : Clause -> Clause -> Bool
subset xs ys = all (\x => elem x ys) xs

consistent : Clause -> Bool
consistent xs = not (any (\(n, b) => elem (n, not b) xs) xs)

reduce : DNF -> DNF
reduce clauses =
  let unique = canonical (filter consistent (map canonical clauses))
   in filter (\c => not (any (\d => d /= c && subset d c) unique)) unique

normal : Face -> DNF
normal Bottom = []
normal Top = [[]]
normal (Endpoint n b) = [[(n, b)]]
normal (Disjunction x y) = reduce (normal x ++ normal y)
normal (Conjunction x y) =
  reduce (concatMap (\a => map (\b => a ++ b) (normal y)) (normal x))


||| Old face entailment algorithm for differential tests only.
public export
referenceEntails : Face -> Face -> Bool
referenceEntails premise conclusion =
  all (\p => any (\q => subset q p) (normal conclusion)) (normal premise)
