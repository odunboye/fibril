module Main

import Data.List
import Data.String
import System
import System.Clock
import Workloads

%default total

-- Each action consumes the result before the next iteration.
runBatch : Nat -> Workload -> Nat -> IO Nat
runBatch Z workload size = pure 0
runBatch (S rest) workload size = do
  if runWorkload workload size rest
     then map S (runBatch rest workload size)
     else runBatch rest workload size

fail : String -> IO ()
fail message = do
  putStrLn message
  exitFailure

main : IO ()
main = do
  args <- getArgs
  case drop 1 args of
    [name, sizeText, iterationsText] =>
      case (parseWorkload name, the (Maybe Nat) (parsePositive sizeText),
            the (Maybe Nat) (parsePositive iterationsText)) of
        (Just workload, Just size, Just iterations) =>
          if size > 0 && size <= 6 && iterations > 0 && iterations <= 1000
             then do
               start <- clockTime Monotonic
               passed <- runBatch iterations workload size
               -- Include forcing/formatting the checksum in the timed region.
               let checksum = show passed
               putStrLn ("passed=" ++ checksum)
               end <- clockTime Monotonic
               let elapsed = timeDifference end start
               putStrLn ("elapsed_ns=" ++ show (seconds elapsed * 1000000000 + nanoseconds elapsed))
               if passed == iterations then pure () else exitFailure
             else fail "Require size 1..6 and iterations 1..1000."
        _ => fail "Invalid workload or numeric arguments."
    _ => fail "Usage: fibril-bench substitution|reduction|erased|runtime|interval|face|expose-full|expose-head SIZE ITERATIONS"
