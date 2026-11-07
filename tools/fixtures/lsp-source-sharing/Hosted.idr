-- Test-only adapters and counter-instrumented driver; execution remains Fibril.
module Hosted

import Data.IORef
import Data.List
import Data.String
import System
import Fibril.Core.Size
import Fibril.Elaboration.Expression.Payload
import Fibril.Data.Bytes
import Fibril.Runtime.Binary
import ObservedBinaryDriver
import Fibril.Driver.Resource
import Fibril.Driver.Interactive
import Fibril.Effect.ConsoleProgram
import Fibril.Driver.ModuleCheck
import Fibril.Driver.ModuleGraph

%default covering

hex : Char -> Nat
hex c = if c >= 'a' then cast (ord c - ord 'a' + 10) else cast (ord c - ord '0')

decode : List Char -> List Bits8
decode (a :: b :: rest) = cast (16 * hex a + hex b) :: decode rest
decode _ = []

main : IO ()
main = do
  [_, root, path, input] <- getArgs | _ => exitFailure
  remaining <- newIORef (decode (unpack input))
  reads <- newIORef (the Nat 0)
  writes <- newIORef (the Nat 0)
  flushes <- newIORef (the Nat 0)
  accepted <- newIORef (the (List Bits8) [])
  let host : BinaryAdapters = BinaryHost
        (\capacity => do
          modifyIORef reads S
          pending <- readIORef remaining
          let chunk = take capacity pending
          writeIORef remaining (drop capacity pending)
          pure (Right (if null chunk then Nothing else Just (fromList chunk))))
        (\bytes => do
          modifyIORef writes S
          modifyIORef accepted (++ Fibril.Data.Bytes.toList bytes)
          pure (the (Either BinaryError ()) (Right ())))
        (do modifyIORef flushes S; pure (the (Either BinaryError ()) (Right ())))
  checked <- checkProject root path
  case checked of
    Left err => do putStrLn (renderGraphError err); exitFailure
    Right project => do
      putStrLn ("SIZE " ++ show (coreNodes project.term) ++ " " ++ show (payloadSize project.term))
      case prepareInteractive 4096 4096 project.term of
        Left InteractiveUnsupported => putStrLn "INTERACTIVE_GATE rejected"
        _ => do putStrLn "INTERACTIVE_GATE unexpected"; exitFailure
      resource <- runResourceTerm project.term
      case resource.outcome of
        Left ResourceAdmission => putStrLn "RESOURCE_GATE rejected"
        _ => do putStrLn "RESOURCE_GATE unexpected"; exitFailure
      result <- runBinaryTermWith 4096 4096 4096 8388608 host project.term
      r <- readIORef reads
      w <- readIORef writes
      f <- readIORef flushes
      rest <- readIORef remaining
      out <- readIORef accepted
      putStrLn ("METRICS " ++ show r ++ " " ++ show w ++ " " ++ show f ++ " " ++ show (length rest) ++ " " ++ show (length out))
      putStrLn ("OUTPUT " ++ show out)
      case result of
        Left err => putStrLn ("ERROR " ++ show err)
        Right () => putStrLn "OK"
