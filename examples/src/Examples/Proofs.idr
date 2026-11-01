module Examples.Proofs

import Data.Vect

%default total

||| The result length is guaranteed by the type, without a runtime check.
public export
append : Vect n a -> Vect m a -> Vect (n + m) a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

||| An ordinary function whose result is an equality proof.
public export
plusZeroRight : (n : Nat) -> n + 0 = n
plusZeroRight Z = Refl
plusZeroRight (S n) = cong S (plusZeroRight n)

||| Induction over data; no axioms or unsafe assertions.
public export
mapIdentity : (xs : List a) -> map Prelude.id xs = xs
mapIdentity [] = Refl
mapIdentity (x :: xs) = cong (x ::) (mapIdentity xs)
