-- Current size reports count reachable shared syntax; historical tree records are separate.
module Measure

import System
import Fibril.Driver.ModuleCheck
import Fibril.Driver.ModuleGraph
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Runtime
import Fibril.Core.Erased
import Fibril.Core.SharedProgram
import Fibril.Core.Size
import Fibril.Elaboration.Expression.Payload

covering
main : IO ()
main = do
  [_, root, entry] <- getArgs | _ => putStrLn "usage: measure ROOT ENTRY"
  checked <- checkProject root entry
  case checked of
    Left err => putStrLn (renderGraphError err)
    Right project => case reachableGlobals project.globals project.term of
      Left message => putStrLn message
      Right declarations => putStrLn
        ("CORE_NODES=" ++ show (sharedProgramNodes project.term declarations) ++
         " PAYLOAD=" ++ show (sharedProgramPayload project.term declarations))
