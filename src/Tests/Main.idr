module Tests.Main

import Fibril.Core.Quantity
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.NormalForm
import System
import Data.List

%default total

checks : List (String, Bool)
checks =
  [ ("symbolic involution", equivalent (Reverse (Reverse (Var 0))) (Var 0))
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
    [] => putStrLn "Bootstrap quantity and interval tests passed."
    _ => do
      traverse_ (putStrLn . fst) failed
      exitFailure
