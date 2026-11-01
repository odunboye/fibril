module Tests.CheckReport

import Data.List
import Fibril.Source.Diagnostic
import Fibril.Source.Text
import Fibril.Driver.JSON
import Fibril.Driver.Check
import Fibril.Driver.CheckReport

%default total

public export
checks : List (String, Bool)
checks =
  [ ("JSON escapes quotes and backslashes",
      jsonString "\"\\" == "\"\\\"\\\\\"")
  , ("JSON escapes data controls",
      jsonString (pack [chr 0, chr 10, chr 31]) == "\"\\u0000\\u000a\\u001f\"")
  , ("JSON preserves valid Unicode data",
      jsonString "λ 🌍" == "\"λ 🌍\"")
  , ("check report accepts ordinary values", isAccepted (checkReport "True"))
  , ("check report rejects wrong types", not (isAccepted (checkReport "(True : String)")))
  , ("check report keeps real resolver positions",
      case checkReport "missing" of
        Rejected err => case driverDiagnostic err of
          Just diagnostic => diagnostic.position.line == 1 && diagnostic.position.column == 1
          _ => False
        _ => False)
  , ("check report does not invent core error positions",
      case checkReport "(True : String)" of
        Rejected err => case driverDiagnostic err of Nothing => True; _ => False
        _ => False)
  , ("check report checks descriptions without executing effects",
      isAccepted (checkReport "main : IO Unit\nmain = putStrLn \"not printed\""))
  ]
