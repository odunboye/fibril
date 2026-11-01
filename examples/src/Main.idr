module Main

import Examples.Basics
import Examples.Checking
import Examples.Proofs
import Examples.Cubical
import Fibril.Foundation.DeMorgan.Interval
import System
import Data.Vect

%default total

main : IO ()
main = do
  putStrLn greeting
  printLn (linearIdentity 42)
  printLn (Examples.Proofs.append [1, 2] [3])
  -- These bindings are checked proofs, not Boolean tests.
  let arithmeticProof = plusZeroRight 10
  let listProof = mapIdentity [1, 2, 3]
  let syntaxProof = substitutionIdentity (Meet (Var 0) (Reverse (Var 1)))
  if deMorganCheck && boundaryCheck && identityChecks
     then putStrLn "Idris proofs checked; erased core identity and cubical infrastructure checks passed."
     else do
       putStrLn "Cubical example check failed."
       exitFailure
