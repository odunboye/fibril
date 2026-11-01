module Tests.Console

import Data.List
import Fibril.Core.Term
import Fibril.Effect.Console
import Fibril.Source.Console
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.StringLiteral
import Fibril.Driver.Check
import Fibril.Driver.Evaluate

%default total

hello : String
hello = "main : IO Unit\nmain = putStrLn \"Hello, world!\""

rejects : String -> Bool
rejects source = case prepareSource source of
  Left _ => True
  Right _ => False

public export
checks : List (String, Bool)
checks =
  [ ("console hello produces action data",
      case prepareSource hello of
        Right (ConsoleSource entry) => case entry.action of
          PrintLine value => value == "Hello, world!"
        _ => False)
  , ("console check is explicitly separate profile",
      case checkSource False hello of
        Right lines => elem "Type: IO Unit" lines &&
          elem "Console entry checking: accepted (restricted profile, not ordinary core checking)" lines
        Left _ => False)
  , ("console cannot be checked as an erased proof",
      case checkSourceDetailed True hello of
        Left ErasedConsole => True
        _ => False)
  , ("console cannot enter reference normalization",
      case evaluateSourceDetailed 128 hello of
        Left EffectfulEvaluation => True
        _ => False)
  , ("console cannot resolve into an ordinary core term",
      case resolveSource hello of
        Left (Parsing _) => True
        _ => False)
  , ("console whole source required",
      rejects (hello ++ "\nmain = putStrLn \"second\""))
  , ("console arbitrary primitive rejected",
      rejects "main : IO Unit\nmain = unknown \"message\"")
  , ("console wrong result annotation rejected",
      rejects "main : IO Bool\nmain = putStrLn \"message\"")
  , ("console missing literal rejected",
      rejects "main : IO Unit\nmain = putStrLn")
  , ("console multiple literals rejected",
      rejects (hello ++ " \"second\""))
  , ("console expression after literal rejected",
      rejects (hello ++ " ()"))
  , ("console missing signature rejected",
      rejects "main = putStrLn \"message\"")
  , ("console helper definitions unsupported",
      rejects ("other : Bool\nother = True\n" ++ hello))
  , ("console headers must be separate",
      rejects "main : IO Unit main = putStrLn \"message\"")
  , ("console multiline body with comments",
      case prepareSource "-- entry\r\nmain : IO Unit\r\nmain =\r\n  putStrLn \"λ 🌍 -- text\" -- done\r\n" of
        Right (ConsoleSource entry) => case entry.action of
          PrintLine value => value == "λ 🌍 -- text"
        _ => False)
  , ("console no raw unindented body",
      rejects "main : IO Unit\nmain =\nputStrLn \"message\"")
  , ("strings token preserves exact spelling",
      case lexSource "\"a\\n\\\"\\\\b\"" of
        Right [token] => token.kind == StringToken && token.spelling == "\"a\\n\\\"\\\\b\""
        _ => False)
  , ("strings decode supported escapes without consuming suffix",
      case scanLiteral (At 0 1 1) (unpack "\"a\\n\\\"\\\\b\" tail") of
        Right literal => literal.value == "a\n\"\\b" &&
                         pack literal.original == "\"a\\n\\\"\\\\b\"" &&
                         pack literal.remaining == " tail"
        Left _ => False)
  , ("strings carriage-return and tab escapes",
      case scanLiteral (At 0 1 1) (unpack "\"\\r\\t\"") of
        Right literal => literal.value == "\r\t"
        Left _ => False)
  , ("strings empty literal allowed",
      case prepareSource "main : IO Unit\nmain = putStrLn \"\"" of
        Right (ConsoleSource entry) => case entry.action of
          PrintLine value => value == ""
        _ => False)
  , ("strings unknown escape is located",
      case lexSource "\"x\\q\"" of
        Left (BadString err) => err.position.column == 3
        _ => False)
  , ("strings unterminated EOF is located",
      case lexSource "\"oops" of
        Left (BadString err) => err.position.column == 6
        _ => False)
  , ("strings raw linebreak rejected",
      case lexSource "\"x\nx\"" of
        Left (BadString _) => True
        _ => False)
  , ("strings raw tab rejected",
      case lexSource "\"x\tx\"" of
        Left (BadString _) => True
        _ => False)
  , ("strings never become ordinary core expressions", rejects "\"message\"")
  , ("strings source-wide control policy preserved",
      case lexSource ("\"" ++ pack [chr 0x202E] ++ "\"") of
        Left (InvalidSource _) => True
        _ => False)
  ]
