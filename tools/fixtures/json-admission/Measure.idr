module Measure

import System
import Fibril.Driver.ModuleCheck
import Fibril.Driver.ModuleGraph
import Fibril.Core.Size
import Fibril.Elaboration.Expression.Payload

covering
main : IO ()
main = do
  [_, root, entry] <- getArgs | _ => putStrLn "usage: measure ROOT ENTRY"
  checked <- checkProject root entry
  case checked of
    Left err => putStrLn (renderGraphError err)
    Right project => putStrLn
      ("CORE_NODES=" ++ show (coreNodes project.term) ++
       " PAYLOAD=" ++ show (payloadSize project.term))
