-- Parse the complete restricted console entry; arguments are checked separately.
module Fibril.Source.Console

import Data.List
import Fibril.Source.Syntax
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Parser

%default total

||| Prototype source-action cap, not a time/memory or host-API quota.
public export
maximumConsoleActions : Nat
maximumConsoleActions = 64

||| Unchecked source expressions, not executable actions or typing certificates.
public export
record ConsoleEntry where
  constructor ConsoleMain
  span : SourceSpan
  arguments : List Expr

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
  argument : Expr
  remaining : List Token

tokenEnd : Position -> List Token -> Position
tokenEnd fallback [] = fallback
tokenEnd fallback (token :: rest) = tokenEnd token.span.finish rest

parseAction : Bool -> Position -> List Token -> Either ParseError ParsedAction
parseAction oneLine end tokens = do
  (primitive, afterPrimitive) <- named "putStrLn" end tokens
  let chunks : (List Token, List Token) =
        if oneLine then Data.List.span (\token => token.span.start.line == primitive.span.start.line) afterPrimitive
                   else (afterPrimitive, [])
  let (argumentTokens, remaining) = chunks
  argument <- parseExpression 256 (tokenEnd primitive.span.finish argumentTokens) argumentTokens
  Right (Parsed (Between primitive.span.start (extent argument).finish) argument remaining)

parseActions : Nat -> Position -> Nat -> Nat -> Position -> List Token ->
               Either ParseError (List Expr, Position)
parseActions budget end column previous finish [] = Right ([], finish)
parseActions Z end column previous finish (token :: _) =
  Left (ParseFailure token.span.start "Console action count budget exhausted")
parseActions (S budget) end column previous finish tokens@(token :: _) = do
  if token.span.start.column /= column || token.span.start.line <= previous
     then Left (ParseFailure token.span.start
                "Console actions must occupy separate equally indented lines")
     else Right ()
  parsed <- parseAction True end tokens
  (rest, final) <- parseActions budget end column parsed.span.finish.line
                               parsed.span.finish parsed.remaining
  Right (parsed.argument :: rest, final)

parseBody : Nat -> Position -> Token -> List Token ->
            Either ParseError (List Expr, Position)
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
         if not (all (\token => token.span.start.line == definition.span.start.line ||
                                token.span.start.column > 1) (doToken :: rest))
            then Left (ParseFailure doToken.span.start "Console continuation lines must be indented")
            else Right ()
         parsed <- parseAction False end (doToken :: rest)
         Right ([parsed.argument], parsed.span.finish)
parseBody budget end definition [] = Left (ParseFailure end "Expected console action")

||| Parse ordinary arguments, optionally in a bounded nonempty flat do block.
||| Syntax only: the driver must check and prepare all arguments before executing.
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
  (arguments, finish) <- parseBody budget end definition rest
  Right (ConsoleMain (Between mainName.span.start finish) arguments)

public export
parseConsole : Position -> List Token -> Either ParseError ConsoleEntry
parseConsole = parseConsoleWithBudget maximumConsoleActions
