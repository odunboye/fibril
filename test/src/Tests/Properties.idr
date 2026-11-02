module Tests.Properties

import Data.Fin
import Data.List
import Data.Vect
import Hedgehog
import Tests.Reference.Interval
import Tests.Reference.Face
import Fibril.Foundation.DeMorgan.Sorted
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Pretty
import Fibril.Core.Reduction
import Fibril.Core.Reduction.Fuel
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.NormalForm
import Fibril.Foundation.DeMorgan.Face

%default total

-- Test-local displays keep counterexamples readable without changing core APIs.
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
atom Z = element [Universe 0, Universe 1, UnitType, UnitValue, BoolType, BoolTrue, BoolFalse,
                  StringType, StringValue "", StringValue "λ 🌍"]
atom (S n) = choice [element [Universe 0, Universe 1, UnitType, UnitValue, BoolType, BoolTrue, BoolFalse,
                                StringType, StringValue "", StringValue "λ 🌍"], Variable <$> finGen n]

-- Bounds and binders are constructed together: shrinking never creates
-- dangling indices. These are scoped, not necessarily well-typed terms.
termGen : Nat -> (n : Nat) -> Gen (Term n)
termGen Z n = atom n
termGen (S depth) n =
  choice
    [ atom n
    , Sigma <$> quantityGen <*> quantityGen <*> termGen depth n <*> termGen depth (S n)
    , PairValue <$> termGen depth n <*> termGen depth n <*> termGen depth n
    , Pi <$> quantityGen <*> termGen depth n <*> termGen depth (S n)
    , Lambda <$> quantityGen <*> termGen depth n <*> termGen depth (S n)
    , Apply <$> termGen depth n <*> termGen depth n
    , UnitCase <$> termGen depth n <*> termGen depth n
    , StringAppend <$> termGen depth n <*> termGen depth n
    , StringEqual <$> termGen depth n <*> termGen depth n
    , BoolCase <$> termGen depth n <*> termGen depth n <*> termGen depth n
    , IOType <$> termGen depth n
    , IOPure <$> termGen depth n
    , WriteLine <$> termGen depth n
    , IOBind <$> termGen depth n <*> termGen depth n <*> termGen depth n <*> termGen depth n
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

intervalOracle : Property
intervalOracle = property $ do
  [x, y] <- forAll (vect 2 (intervalGen 3))
  equivalent x y === referenceEquivalent x y
  equivalent x (Reverse (Reverse x)) === referenceEquivalent x (Reverse (Reverse x))

faceOracle : Property
faceOracle = property $ do
  [x, y] <- forAll (vect 2 (intervalGen 3))
  let premise = Conjunction (endpointFace x False) (endpointFace y True)
  let conclusion = Disjunction (endpointFace y False) (endpointFace x True)
  entails premise conclusion === referenceEntails premise conclusion
  entails premise (endpointFace x False) === referenceEntails premise (endpointFace x False)

sortedOracle : Property
sortedOracle = property $ do
  [xs, ys] <- forAll (vect 2 (list (linear 0 20) (the (Gen Nat) (element [0, 1, 2, 3, 4, 5]))))
  let left = canonicalSorted (the (List Nat) xs)
  let right = canonicalSorted (the (List Nat) ys)
  left === nub (sort xs)
  subsetSorted left right === all (\x => elem x right) left

sameReduction : ReductionResult n -> ReductionResult n -> Bool
sameReduction (Normal left) (Normal right) = sameSyntax left right
sameReduction (OutOfFuel left) (OutOfFuel right) = sameSyntax left right
sameReduction _ _ = False

fuelSplitting : Property
fuelSplitting = property $ do
  term <- forAll (choice [termGen 3 2, UnitCase UnitValue <$> termGen 3 2])
  [first, extra] <- forAll (vect 2 (element [0, 1, 2]))
  let initial = normalize first term
  classify "initial exhaustion" (case initial of OutOfFuel _ => True; _ => False)
  assert (sameReduction (normalize (first + extra) term)
                        (continueNormalization extra initial))

||| Run randomized, shrinking properties in addition to deterministic regressions.
||| A successful run is evidence from samples, not a proof of these laws.
public export
runProperties : IO Bool
runProperties = checkGroup (MkGroup "Fibril structural properties"
  [ ("normalization fuel splits and resumes", fuelSplitting)
  , ("sorted helpers match simple algorithms", sortedOracle)
  , ("interval solver matches frozen oracle", intervalOracle)
  , ("face solver matches frozen oracle", faceOracle)
  , ("term renaming identity", renameIdentity)
  , ("term substitution identity", substitutionIdentity)
  , ("term substitution composition", substitutionComposition)
  , ("weakening then instantiation", weakeningInstantiation)
  , ("interval involution", intervalInvolution)
  , ("De Morgan law", deMorgan)
  , ("endpoint substitution compatibility", endpointSubstitution)
  , ("endpoint disjointness", endpointDisjoint)
  ])
