-- Validate the entire restricted main : IO Unit console entry before execution.
module Fibril.Source.Console

import Fibril.Effect.Console
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.StringLiteral
import Fibril.Source.Parser

%default total

public export
record ConsoleEntry where
  constructor ConsoleMain
  span : SourceSpan
  action : ConsoleAction

||| Only a leading explicit IO signature selects this separate console profile.
public export
consoleAhead : List Token -> Bool
consoleAhead (Located Name _ _ :: Located Colon _ _ :: Located Name name _ :: _) =
  name == "IO"
consoleAhead _ = False

named : String -> Position -> List Token -> Either ParseError (Token, List Token)
named name end tokens = do
  (token, rest) <- expect Name end tokens
  if token.spelling == name then Right (token, rest)
     else Left (ParseFailure token.span.start ("Expected " ++ name ++ ", found " ++ token.spelling))

||| No arbitrary expressions, imports, helper declarations, or sequencing yet.
||| Complete token consumption is mandatory, even after a valid print request.
public export
parseConsole : Position -> List Token -> Either ParseError ConsoleEntry
parseConsole end tokens = do
  (mainName, rest) <- named "main" end tokens
  (_, rest) <- expect Colon end rest
  (_, rest) <- named "IO" end rest
  (unit, rest) <- expect UnitKeyword end rest
  if mainName.span.start.column /= 1 || unit.span.finish.line /= mainName.span.start.line
     then Left (ParseFailure mainName.span.start "Console signature must be a column-one main : IO Unit line")
     else Right ()
  (definition, rest) <- named "main" end rest
  (equals, rest) <- expect Equals end rest
  if definition.span.start.column /= 1 ||
     definition.span.start.line <= unit.span.finish.line ||
     equals.span.start.line /= definition.span.start.line
     then Left (ParseFailure definition.span.start "Console definition requires its own column-one main = header")
     else Right ()
  (primitive, rest) <- named "putStrLn" end rest
  (literal, rest) <- expect StringToken end rest
  if (primitive.span.start.line > definition.span.start.line && primitive.span.start.column == 1) ||
     (literal.span.start.line > definition.span.start.line && literal.span.start.column == 1)
     then Left (ParseFailure primitive.span.start "Console continuation lines must be indented")
     else Right ()
  decoded <- case scanLiteral literal.span.start (unpack literal.spelling) of
    Left err => Left (ParseFailure err.position err.message)
    Right decoded => Right decoded
  case rest of
    extra :: _ => Left (ParseFailure extra.span.start "Unexpected tokens after console entry")
    [] => case decoded.remaining of
      [] => Right (ConsoleMain (Between mainName.span.start literal.span.finish)
                             (PrintLine decoded.value))
      _ => Left (ParseFailure literal.span.start "Malformed console string token")
