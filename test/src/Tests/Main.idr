module Tests.Main

import Fibril.Core.Quantity
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.NormalForm
import Fibril.Foundation.DeMorgan.Face
import System
import Data.List

%default total

-- Small exhaustive corpus checks catch polarity/substitution mistakes.
samples : List (Interval Nat)
samples =
  let atoms = [Zero, One, Var 0, Var 1]
   in atoms ++ map Reverse atoms ++
      concatMap (\x => concatMap (\y => [Meet x y, Join x y]) atoms) atoms

replacement : Nat -> Interval Nat
replacement Z = Reverse (Var 1)
replacement (S _) = Meet (Var 0) (Var 1)

endpointSubstitutionLaw : Bool
endpointSubstitutionLaw =
  all (\term => all (\b =>
    equivalentFace
      (endpointFace (substitute replacement term) b)
      (substituteFace replacement (endpointFace term b))) [False, True]) samples

endpointDisjointLaw : Bool
endpointDisjointLaw =
  all (\term => equivalentFace
    (Conjunction (endpointFace term False) (endpointFace term True)) Bottom) samples

checks : List (String, Bool)
checks =
  [ ("endpoint substitution corpus", endpointSubstitutionLaw)
  , ("endpoint disjointness corpus", endpointDisjointLaw)
  , ("endpoint of zero", equivalentFace (endpointFace Zero False) Top)
  , ("endpoint of one", equivalentFace (endpointFace One False) Bottom)
  , ("meet zero face", equivalentFace (endpointFace (Meet (Var 0) (Var 1)) False)
      (Disjunction (Endpoint 0 False) (Endpoint 1 False)))
  , ("join one face", equivalentFace (endpointFace (Join (Var 0) (Var 1)) True)
      (Disjunction (Endpoint 0 True) (Endpoint 1 True)))
  , ("reverse swaps endpoints", equivalentFace (endpointFace (Reverse (Var 0)) False)
      (Endpoint 0 True))
  , ("face identity substitution", equivalentFace
      (substituteFace Var (Conjunction (Endpoint 0 False) (Endpoint 1 True)))
      (Conjunction (Endpoint 0 False) (Endpoint 1 True)))
  , ("face endpoint substitution", equivalentFace
      (substituteFace (const Zero) (Endpoint 0 False)) Top)
  , ("face compound substitution", equivalentFace
      (substituteFace (\n => Meet (Var n) (Var 2)) (Endpoint 0 True))
      (Conjunction (Endpoint 0 True) (Endpoint 2 True)))
  , ("substitution preserves contradiction", equivalentFace
      (substituteFace (const (Join (Var 0) (Var 1)))
        (Conjunction (Endpoint 0 False) (Endpoint 0 True))) Bottom)
  , ("boundary excluded middle still not top", not (equivalentFace
      (endpointFace (Join (Var 0) (Reverse (Var 0))) True) Top))
  , ("face contradiction", equivalentFace
      (Conjunction (Endpoint 0 False) (Endpoint 0 True)) Bottom)
  , ("face endpoints not exhaustive", not (equivalentFace
      (Disjunction (Endpoint 0 False) (Endpoint 0 True)) Top))
  , ("face conjunction entails factor", entails
      (Conjunction (Endpoint 0 False) (Endpoint 1 True)) (Endpoint 0 False))
  , ("face disjunction not entails factor", not (entails
      (Disjunction (Endpoint 0 False) (Endpoint 1 True)) (Endpoint 0 False)))
  , ("face bottom entails anything", entails Bottom (Endpoint 0 False))
  , ("face top not entails endpoint", not (entails Top (Endpoint 0 False)))
  , ("face absorption", equivalentFace
      (Disjunction (Endpoint 0 False)
        (Conjunction (Endpoint 0 False) (Endpoint 1 True))) (Endpoint 0 False))
  , ("face distribution", equivalentFace
      (Conjunction (Endpoint 0 False) (Disjunction (Endpoint 1 False) (Endpoint 2 True)))
      (Disjunction (Conjunction (Endpoint 0 False) (Endpoint 1 False))
                   (Conjunction (Endpoint 0 False) (Endpoint 2 True))))
  , ("face inconsistent branch eliminated", equivalentFace
      (Disjunction (Conjunction (Endpoint 0 False) (Endpoint 0 True))
                   (Endpoint 1 True)) (Endpoint 1 True))
  , ("face distinct dimensions", not (entails (Endpoint 0 False) (Endpoint 1 False)))
  , ("symbolic involution", equivalent (Reverse (Reverse (Var 0))) (Var 0))
  , ("symbolic De Morgan", equivalent (Reverse (Meet (Var 0) (Var 1)))
      (Join (Reverse (Var 0)) (Reverse (Var 1))))
  , ("symbolic absorption", equivalent (Join (Var 0) (Meet (Var 0) (Var 1))) (Var 0))
  , ("symbolic distribution", equivalent (Meet (Var 0) (Join (Var 1) (Var 2)))
      (Join (Meet (Var 0) (Var 1)) (Meet (Var 0) (Var 2))))
  , ("symbolic commutativity", equivalent (Meet (Var 0) (Var 1)) (Meet (Var 1) (Var 0)))
  , ("symbolic idempotence", equivalent (Join (Var 0) (Var 0)) (Var 0))
  , ("symbolic bounds", equivalent (Meet (Var 0) One) (Join Zero (Var 0)))
  , ("no excluded middle", not (equivalent (Join (Var 0) (Reverse (Var 0))) One))
  , ("no complement cancellation", not (equivalent (Meet (Var 0) (Reverse (Var 0))) Zero))
  , ("distinct generators", not (equivalent (Var 0) (Var 1)))
  , ("erased notation", show Erased == "0")
  , ("linear notation", show Linear == "1")
  , ("unrestricted notation", show Unrestricted == "unrestricted")
  , ("distinct quantities", not (Erased == Linear) && not (Linear == Unrestricted))
  , ("zero endpoint", not (atVertex (const False) (the (Interval Nat) Zero)))
  , ("one endpoint", atVertex (const False) (the (Interval Nat) One))
  , ("variable endpoint", atVertex (const True) (Var Z))
  , ("reversal endpoint", not (atVertex (const True) (Reverse (Var Z))))
  , ("meet endpoints", not (atVertex (const True) (Meet (Var Z) Zero)))
  , ("join endpoints", atVertex (const False) (Join (Var Z) One))
  , ("substitution at endpoint",
      atVertex (const False)
        (substitute (\n => the (Interval Nat) One) (Var Z)))
  , ("substitution under reversal",
      not (atVertex (const False)
        (substitute (\n => the (Interval Nat) One) (Reverse (Var Z)))))
  , ("double reversal",
      atVertex (const True) (Reverse (Reverse (Var Z))))
  , ("De Morgan at endpoint",
      atVertex (const False) (Reverse (Meet (Var Z) One)) ==
      atVertex (const False) (Join (Reverse (Var Z)) (Reverse One)))
  ]

main : IO ()
main = do
  let failed = filter (not . snd) checks
  case failed of
    [] => putStrLn "Bootstrap quantity, interval, and face tests passed."
    _ => do
      traverse_ (putStrLn . fst) failed
      exitFailure
