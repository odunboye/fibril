-- Quoted data decoding shared by ordinary and console source parsing.
module Fibril.Source.StringLiteral

import Fibril.Source.Text

%default total

public export
record LiteralError where
  constructor LiteralFailure
  position : Position
  message : String

public export
Show LiteralError where
  show err = show err.position ++ ": " ++ err.message

||| Original source spelling and decoded data, with unconsumed source.
public export
record ParsedLiteral where
  constructor Quoted
  original : List Char
  value : String
  remaining : List Char

escape : Char -> Maybe Char
escape '"' = Just '"'
escape '\\' = Just '\\'
escape 'n' = Just '\n'
escape 'r' = Just '\r'
escape 't' = Just '\t'
escape _ = Nothing

collect : Position -> List Char -> List Char -> List Char ->
          Either LiteralError ParsedLiteral
collect at [] raw decoded = Left (LiteralFailure at "Unterminated string literal")
collect at ('"' :: rest) raw decoded =
  Right (Quoted (reverse ('"' :: raw)) (pack (reverse decoded)) rest)
collect at ('\\' :: []) raw decoded = Left (LiteralFailure at "Unterminated string escape")
collect at ('\\' :: char :: rest) raw decoded =
  case escape char of
    Nothing => Left (LiteralFailure at ("Unsupported string escape: " ++ show char))
    Just value => collect (advancePosition at ['\\', char]) rest
                          (char :: '\\' :: raw) (value :: decoded)
collect at (char :: rest) raw decoded =
  if char == '\n' || char == '\r'
     then Left (LiteralFailure at "Raw line breaks are not allowed in string literals")
  else if char == '\t'
     then Left (LiteralFailure at "Raw tabs must be escaped in string literals")
     else case validateText (pack [char]) of
       Left err => Left (LiteralFailure at (show err.problem))
       Right _ => collect (advancePosition at [char]) rest (char :: raw) (char :: decoded)

||| Scan one double-quoted literal; supports quote/backslash and n/r/t escapes.
||| Raw controls/line breaks and unknown escapes fail. This decodes data only.
public export
scanLiteral : Position -> List Char -> Either LiteralError ParsedLiteral
scanLiteral at ('"' :: rest) = collect (advancePosition at ['"']) rest ['"'] []
scanLiteral at _ = Left (LiteralFailure at "Expected opening string quote")
