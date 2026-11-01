module Fibril.Driver.Symbols

import Data.List
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Symbol
import Fibril.Source.Navigation
import Fibril.Source.File
import Fibril.Source.Diagnostic
import Fibril.Driver.Check

%default total

positionJSON : Position -> String
positionJSON at = "{\"offset\":" ++ show at.offset ++ ",\"line\":" ++ show at.line ++
                  ",\"column\":" ++ show at.column ++ "}"

spanJSON : SourceSpan -> String
spanJSON span = "{\"start\":" ++ positionJSON span.start ++
                ",\"end\":" ++ positionJSON span.finish ++ "}"

symbolJSON : DocumentSymbol -> String
symbolJSON symbol =
  -- Names are lexer-validated ASCII identifiers; no JSON quote/control characters.
  "{\"name\":\"" ++ symbol.name ++ "\",\"quantity\":\"" ++ show symbol.quantity ++
  "\",\"range\":" ++ spanJSON symbol.range ++
  ",\"selection\":" ++ spanJSON symbol.selection ++
  ",\"definitionSelection\":" ++ spanJSON symbol.definitionSelection ++ "}"

public export
renderSymbols : List DocumentSymbol -> String
renderSymbols symbols =
  "{\"version\":1,\"coordinates\":\"unicode-scalars;offset=0;line=1;column=1\",\"symbols\":[" ++
  concat (intersperse "," (map symbolJSON symbols)) ++ "]}"

public export
referencesFile : Nat -> Nat -> String -> IO (Either String (List String))
referencesFile line column path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (renderFileError path (show err))
    Right source => case referencesAt source line column of
      Right references => Right
        ["{\"version\":1,\"coordinates\":\"unicode-scalars;offset=0;line=1;column=1\",\"references\":[" ++
         concat (intersperse "," (map spanJSON references)) ++ "]}"]
      Left (SymbolLexical err) =>
        Left (renderDriverError path source (FrontendFailure (Lexical err)))
      Left (SymbolParsing err) =>
        Left (renderDriverError path source (FrontendFailure (Parsing err)))

public export
definitionFile : Nat -> Nat -> String -> IO (Either String (List String))
definitionFile line column path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (renderFileError path (show err))
    Right source => case definitionAt source line column of
      Right target => Right
        ["{\"version\":1,\"coordinates\":\"unicode-scalars;offset=0;line=1;column=1\",\"definition\":" ++
         maybe "null" spanJSON target ++ "}"]
      Left (SymbolLexical err) =>
        Left (renderDriverError path source (FrontendFailure (Lexical err)))
      Left (SymbolParsing err) =>
        Left (renderDriverError path source (FrontendFailure (Parsing err)))

||| No prelude installation, name resolution, type checking, or effect execution.
public export
symbolsFile : String -> IO (Either String (List String))
symbolsFile path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (renderFileError path (show err))
    Right source => case documentSymbols source of
      Right symbols => Right [renderSymbols symbols]
      Left (SymbolLexical err) =>
        Left (renderDriverError path source (FrontendFailure (Lexical err)))
      Left (SymbolParsing err) =>
        Left (renderDriverError path source (FrontendFailure (Parsing err)))
