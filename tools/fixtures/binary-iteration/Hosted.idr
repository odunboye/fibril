-- Current size reports count reachable shared syntax; historical tree records are separate.
-- Test-only adapters for checked source, not a source-language callback API.
module Hosted

import Data.IORef
import Data.List
import System
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Runtime
import Fibril.Core.Erased
import Fibril.Core.SharedProgram
import Fibril.Core.Size
import Fibril.Data.Bytes
import Fibril.Runtime.Binary
import Fibril.Driver.Binary
import Fibril.Driver.ModuleCheck
import Fibril.Driver.ModuleGraph

%default covering

main : IO ()
main = do
  [_, root, path, mode, size] <- getArgs | _ => exitFailure
  let n : Nat = cast size
  let views = mode == "views-done" || mode == "views-exhausted"
  let input : List Bits8 = if views then [126, 0, 255, 195, 40, 128, 254, 127, 97, 98, 99]
        else if mode == "two" then replicate 1023 97 ++ [58] ++ replicate 1023 97 ++ [58]
        else if mode == "eof" then replicate n 97 else replicate (minus n 1) 97 ++ [58]
  remaining <- newIORef input
  reads <- newIORef (the Nat 0)
  writes <- newIORef (the Nat 0)
  flushes <- newIORef (the Nat 0)
  accepted <- newIORef (the (List Bits8) [])
  let host = BinaryHost
        (\capacity => do
          modifyIORef reads S
          pending <- readIORef remaining
          if mode == "read-error" && length pending <= 2 then pure (Left (BinaryReadFailed empty)) else do
            let chunk = take capacity pending
            writeIORef remaining (drop capacity pending)
            pure (Right (if null chunk then Nothing else Just (fromList chunk))))
        (\bytes => do
          modifyIORef writes S
          let output = toList bytes
          case mode of
            "write-error" => do
              modifyIORef accepted (++ take 1 output)
              pure (Left (BinaryWriteFailed (min 1 (length output))))
            _ => do
              modifyIORef accepted (++ output)
              pure (Right ()))
        (do modifyIORef flushes S
            pure (if mode == "flush-error" then Left BinaryFlushFailed else Right ()))
  checked <- checkProject root path
  case checked of
    Left err => do putStrLn (renderGraphError err); exitFailure
    Right project => do
      declarations <- case reachableGlobals project.globals project.term of
        Left message => do putStrLn message; exitFailure
        Right declarations => pure declarations
      result <- runBinaryTermWithGlobals project.globals 4096 4096 4096 8388608 host project.term
      r <- readIORef reads
      w <- readIORef writes
      f <- readIORef flushes
      rest <- readIORef remaining
      out <- readIORef accepted
      putStrLn ("METRICS " ++ show r ++ " " ++ show w ++ " " ++ show f ++ " " ++ show (length rest) ++ " " ++ show (length out))
      case views of
        True => do
          putStrLn ("OUTPUT " ++ show out)
          putStrLn ("NODES " ++ show (sharedProgramNodes project.term declarations))
        False => pure ()
      case result of
        Left err => putStrLn ("ERROR " ++ show err)
        Right () => putStrLn "OK"
