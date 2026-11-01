-- Structured checking results for editor integrations, not typing certificates.
module Fibril.Driver.CheckReport

import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.UTF8
import Fibril.Source.File
import Fibril.Source.Diagnostic
import Fibril.Driver.Check
import Fibril.Driver.JSON

%default total

public export
data CheckReport = Checked (List String) | Rejected DriverError | LoadFailed LoadError

public export
isAccepted : CheckReport -> Bool
isAccepted (Checked _) = True
isAccepted _ = False

public export
checkReport : String -> CheckReport
checkReport source = case checkSourceDetailed False source of
  Right lines => Checked lines
  Left err => Rejected err

public export
checkFileReport : String -> IO CheckReport
checkFileReport path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => LoadFailed err
    Right source => checkReport source

stage : DriverError -> String
stage (FrontendFailure (Lexical (InvalidSource _))) = "source-validation"
stage (FrontendFailure (Lexical _)) = "lexing"
stage (FrontendFailure (Parsing _)) = "parsing"
stage (FrontendFailure (Resolving _)) = "resolution"
stage (FrontendFailure (PreludeUnavailable _)) = "prelude"
stage (ErasedFailure _) = "erased-checking"
stage (RuntimeFailure _) = "runtime-checking"
stage EvaluationLimit = "evaluation"
stage (PostReductionFailure _) = "post-reduction"
stage (ConsoleFailure _) = "io-planning"

diagnosticJSON : String -> String -> Maybe Position -> Maybe Nat -> String
diagnosticJSON stage message point byteOffset = jsonObject
  [("severity", jsonString "error"), ("stage", jsonString stage),
   ("message", jsonString message),
   ("position", maybe "null" jsonPosition point),
   ("byteOffset", maybe "null" show byteOffset)]

reportJSON : Bool -> List String -> List String -> String
reportJSON accepted lines diagnostics = protocolJSON
  [("accepted", if accepted then "true" else "false"),
   ("report", jsonArray (map jsonString lines)),
   ("diagnostics", jsonArray diagnostics)]

public export
renderCheckReport : CheckReport -> String
renderCheckReport (Checked lines) = reportJSON True lines []
renderCheckReport (Rejected err) =
  let point = map position (driverDiagnostic err)
   in reportJSON False [] [diagnosticJSON (stage err) (show err) point Nothing]
renderCheckReport (LoadFailed (InvalidText err)) =
  reportJSON False [] [diagnosticJSON "source-validation" (show err) (Just err.position) Nothing]
renderCheckReport (LoadFailed (InvalidUTF8 err)) =
  reportJSON False [] [diagnosticJSON "decoding" (show err) Nothing (Just err.byteOffset)]
renderCheckReport (LoadFailed err) =
  reportJSON False [] [diagnosticJSON "loading" (show err) Nothing Nothing]
