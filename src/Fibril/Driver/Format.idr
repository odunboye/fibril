module Fibril.Driver.Format

import Fibril.Source.File
import Fibril.Source.Format
import Fibril.Source.Document
import Fibril.Source.Diagnostic
import Fibril.Driver.Check
import Fibril.Driver.JSON

%default total

failure : String -> String -> FormatError -> String
failure path source (FormatDocument (SymbolLexical err)) =
  renderDriverError path source (FrontendFailure (Lexical err))
failure path source (FormatDocument (SymbolParsing err)) =
  renderDriverError path source (FrontendFailure (Parsing err))
failure path source FormatShapeChanged =
  renderFileError path "Formatting refused: candidate parsing/structure differs"
failure path source FormatSizeLimit =
  renderFileError path "Formatting input/output exceeds 65536 UTF-8 bytes"

||| Snapshot protocol for editor consumers; original text is an explicit identity
||| check, not a signature or proof. Uses the same guarded formatting operation.
public export
formatFileReport : String -> IO (Either String (List String))
formatFileReport path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (renderFileError path (show err))
    Right source => case formatSource source of
      Left err => Left (failure path source err)
      Right formatted => Right [protocolJSON [("original", jsonString source),
                                              ("formatted", jsonString formatted)]]

||| stdout-only formatting, or empty success for --check. No source writes.
public export
formatFile : Bool -> String -> IO (Either String String)
formatFile checking path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (renderFileError path (show err))
    Right source => case formatSource source of
      Left err => Left (failure path source err)
      Right formatted => if checking
         then if source == formatted then Right ""
                 else Left (renderFileError path "Formatting required")
         else Right formatted
