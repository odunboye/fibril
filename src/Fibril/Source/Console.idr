-- Validate the entire restricted main : IO Unit console entry before execution.
module Fibril.Source.Console

import Fibril.Effect.Console
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Parser

%default total

||| Prototype source-action cap, not a time/memory or host-API quota.
public export
maximumConsoleActions : Nat
maximumConsoleActions = 64

public export
record ConsoleEntry where
  constructor ConsoleMain
  span : SourceSpan
  actions : List ConsoleAction

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

record ParsedAction where
  constructor Parsed
  span : SourceSpan
  literalStart : Position
  action : ConsoleAction
  remaining : List Token

parseAction : Position -> List Token -> Either ParseError ParsedAction
parseAction end tokens = do
  (primitive, rest) <- named "putStrLn" end tokens
  (literal, rest) <- expect StringToken end rest
  value <- literalValue literal
  Right (Parsed (Between primitive.span.start literal.span.finish)
                literal.span.start (PrintLine value) rest)

-- Every source action is a whole physical line at the first action's column.
-- Explicit budget recursion bounds actions independently of the file-byte cap.
parseActions : Nat -> Position -> Nat -> Nat -> Position -> List Token ->
               Either ParseError (List ConsoleAction, Position)
parseActions budget end column previous finish [] = Right ([], finish)
parseActions Z end column previous finish (token :: _) =
  Left (ParseFailure token.span.start "Console action count budget exhausted")
parseActions (S budget) end column previous finish tokens@(token :: _) = do
  if token.span.start.column /= column || token.span.start.line <= previous
     then Left (ParseFailure token.span.start
                "Console actions must occupy separate equally indented lines")
     else Right ()
  parsed <- parseAction end tokens
  if parsed.span.start.line /= parsed.span.finish.line
     then Left (ParseFailure parsed.span.start "A do-block print must fit on one source line")
     else Right ()
  (rest, final) <- parseActions budget end column parsed.span.finish.line
                               parsed.span.finish parsed.remaining
  Right (parsed.action :: rest, final)

parseBody : Nat -> Position -> Token -> List Token ->
            Either ParseError (List ConsoleAction, Position)
parseBody budget end definition (doToken :: rest) =
  if doToken.kind == Name && doToken.spelling == "do"
     then do
       if doToken.span.start.line > definition.span.start.line &&
          doToken.span.start.column == 1
          then Left (ParseFailure doToken.span.start "Console continuation lines must be indented")
          else Right ()
       let minimum = if doToken.span.start.line == definition.span.start.line
                        then 1 else doToken.span.start.column
       case rest of
         [] => Left (ParseFailure end "Console do block requires at least one action")
         first :: _ =>
           if first.span.start.line <= doToken.span.start.line || first.span.start.column <= minimum
              then Left (ParseFailure first.span.start "Console do actions require indented following lines")
              else parseActions budget end first.span.start.column doToken.span.start.line
                                doToken.span.finish rest
     else case budget of
       Z => Left (ParseFailure doToken.span.start "Console action count budget exhausted")
       S _ => do
         parsed <- parseAction end (doToken :: rest)
         if (parsed.span.start.line > definition.span.start.line && parsed.span.start.column == 1) ||
            (parsed.literalStart.line > definition.span.start.line && parsed.literalStart.column == 1)
            then Left (ParseFailure parsed.span.start "Console continuation lines must be indented")
            else Right ()
         case parsed.remaining of
           extra :: _ => Left (ParseFailure extra.span.start "Unexpected tokens after console entry")
           [] => Right ([parsed.action], parsed.span.finish)
parseBody budget end definition [] = Left (ParseFailure end "Expected console action")

||| Restricted literal printing, optionally in a nonempty flat do block.
||| Complete validation precedes execution; no variables, bind, or general IO.
public export
parseConsoleWithBudget : Nat -> Position -> List Token -> Either ParseError ConsoleEntry
parseConsoleWithBudget budget end tokens = do
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
  (actions, finish) <- parseBody budget end definition rest
  Right (ConsoleMain (Between mainName.span.start finish) actions)

public export
parseConsole : Position -> List Token -> Either ParseError ConsoleEntry
parseConsole = parseConsoleWithBudget maximumConsoleActions
