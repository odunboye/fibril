-- Current size reports count reachable shared syntax; historical tree records are separate.
-- Test adapter only: checks actual source and runs the real binary driver.
module Harness

import Data.IORef
import Data.List
import System
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Runtime
import Fibril.Core.Erased
import Fibril.Core.SharedProgram
import Fibril.Core.Size
import Fibril.Elaboration.Expression.Payload
import Fibril.Data.Bytes
import Fibril.Runtime.Binary
import Fibril.Driver.Binary
import Fibril.Driver.ModuleCheck
import Fibril.Driver.ModuleGraph

%default covering

main : IO ()
main = do
  [_, mode, root, path] <- getArgs | _ => exitFailure
  checked <- checkProject root path
  case checked of
    Left err => do putStrLn (renderGraphError err); exitFailure
    Right project => do
      declarations <- case reachableGlobals project.globals project.term of
        Left message => do putStrLn message; exitFailure
        Right declarations => pure declarations
      putStrLn ("SIZE " ++ show (sharedProgramNodes project.term declarations) ++ " " ++ show (sharedProgramPayload project.term declarations))
      if mode == "measure" then pure () else do
        reads <- newIORef (the Nat 0)
        writes <- newIORef (the Nat 0)
        flushes <- newIORef (the Nat 0)
        accepted <- newIORef (the (List Bits8) [])
        let host : BinaryAdapters = BinaryHost
              (\capacity => do
                modifyIORef reads S
                pure (the (Either BinaryError (Maybe Fibril.Data.Bytes.Bytes)) (Right Nothing)))
              (\bytes => do
                modifyIORef writes S
                modifyIORef accepted (++ Fibril.Data.Bytes.toList bytes)
                pure (the (Either BinaryError ()) (Right ())))
              (do
                modifyIORef flushes S
                pure (the (Either BinaryError ()) (Right ())))
        result <- runBinaryTermWithGlobals project.globals 4096 4096 4096 8388608 host project.term
        r <- readIORef reads
        w <- readIORef writes
        f <- readIORef flushes
        out <- readIORef accepted
        putStrLn ("METRICS " ++ show r ++ " " ++ show w ++ " " ++ show f)
        putStrLn ("OUTPUT " ++ show out)
        case result of
          Left err => do putStrLn ("ERROR " ++ show err); exitFailure
          Right () => putStrLn "OK"
