module Tests.Properties

import Data.Fin
import Data.Vect
import Hedgehog
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.NormalForm
import Fibril.Foundation.DeMorgan.Face

%default total

-- Test-local displays keep counterexamples readable without changing core APIs.
Show (Term n) where
  show (Variable i) = "v" ++ show (finToNat i)
  show (Universe l) = "Type" ++ show l
  show (Pi q a b) = "(Pi " ++ show q ++ " " ++ show a ++ " " ++ show b ++ ")"
  show (Lambda q a b) = "(Lam " ++ show q ++ " " ++ show a ++ " " ++ show b ++ ")"
  show (Apply f x) = "(" ++ show f ++ " @ " ++ show x ++ ")"

Show (Interval Nat) where
  show Zero = "0"
  show One = "1"
  show (Var n) = "i" ++ show n
  show (Meet x y) = "(" ++ show x ++ " & " ++ show y ++ ")"
  show (Join x y) = "(" ++ show x ++ " | " ++ show y ++ ")"
  show (Reverse x) = "~" ++ show x

finGen : (n : Nat) -> Gen (Fin (S n))
finGen Z = pure FZ
finGen (S n) = choice [pure FZ, FS <$> finGen n]

quantityGen : Gen Quantity
quantityGen = element [Erased, Linear, Unrestricted]

atom : (n : Nat) -> Gen (Term n)
atom Z = element [Universe 0, Universe 1]
atom (S n) = choice [pure (Universe 0), pure (Universe 1), Variable <$> finGen n]

-- Bounds and binders are constructed together: shrinking never creates
-- dangling indices. These are scoped, not necessarily well-typed terms.
termGen : Nat -> (n : Nat) -> Gen (Term n)
termGen Z n = atom n
termGen (S depth) n =
  choice
    [ atom n
    , Pi <$> quantityGen <*> termGen depth n <*> termGen depth (S n)
    , Lambda <$> quantityGen <*> termGen depth n <*> termGen depth (S n)
    , Apply <$> termGen depth n <*> termGen depth n
    ]

intervalAtom : Gen (Interval Nat)
intervalAtom = element [Zero, One, Var 0, Var 1, Var 2]

intervalGen : Nat -> Gen (Interval Nat)
intervalGen Z = intervalAtom
intervalGen (S depth) =
  choice
    [ intervalAtom
    , Reverse <$> intervalGen depth
    , Meet <$> intervalGen depth <*> intervalGen depth
    , Join <$> intervalGen depth <*> intervalGen depth
    ]

renameIdentity : Property
renameIdentity = property $ do
  t <- forAll (termGen 4 2)
  assert (sameSyntax (rename id t) t)

substitutionIdentity : Property
substitutionIdentity = property $ do
  t <- forAll (termGen 4 2)
  assert (sameSyntax (substituteTerm Variable t) t)

substitutionComposition : Property
substitutionComposition = property $ do
  t <- forAll (termGen 3 2)
  a <- forAll (termGen 2 1)
  b <- forAll (termGen 2 1)
  c <- forAll (termGen 2 0)
  let first : Fin 2 -> Term 1
      first = \i => case i of
        FZ => a
        FS FZ => b
  let second : Fin 1 -> Term 0
      second = \i => c
  assert (sameSyntax
    (substituteTerm second (substituteTerm first t))
    (substituteTerm (\i => substituteTerm second (first i)) t))

weakeningInstantiation : Property
weakeningInstantiation = property $ do
  t <- forAll (termGen 4 2)
  value <- forAll (termGen 2 2)
  assert (sameSyntax (instantiateTerm value (weaken t)) t)

intervalInvolution : Property
intervalInvolution = property $ do
  x <- forAll (intervalGen 3)
  assert (equivalent (Reverse (Reverse x)) x)

deMorgan : Property
deMorgan = property $ do
  [x, y] <- forAll (vect 2 (intervalGen 3))
  assert (equivalent (Reverse (Meet x y)) (Join (Reverse x) (Reverse y)))

endpointSubstitution : Property
endpointSubstitution = property $ do
  [term, replacement] <- forAll (vect 2 (intervalGen 3))
  assert (equivalentFace
    (endpointFace (substitute (const replacement) term) False)
    (substituteFace (const replacement) (endpointFace term False)))
  assert (equivalentFace
    (endpointFace (substitute (const replacement) term) True)
    (substituteFace (const replacement) (endpointFace term True)))

endpointDisjoint : Property
endpointDisjoint = property $ do
  term <- forAll (intervalGen 3)
  assert (equivalentFace
    (Conjunction (endpointFace term False) (endpointFace term True)) Bottom)

||| Run randomized, shrinking properties in addition to deterministic regressions.
||| A successful run is evidence from samples, not a proof of these laws.
public export
runProperties : IO Bool
runProperties = checkGroup (MkGroup "Fibril structural properties"
  [ ("term renaming identity", renameIdentity)
  , ("term substitution identity", substitutionIdentity)
  , ("term substitution composition", substitutionComposition)
  , ("weakening then instantiation", weakeningInstantiation)
  , ("interval involution", intervalInvolution)
  , ("De Morgan law", deMorgan)
  , ("endpoint substitution compatibility", endpointSubstitution)
  , ("endpoint disjointness", endpointDisjoint)
  ])
