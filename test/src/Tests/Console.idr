module Tests.Console

import Data.List
import Fibril.Core.Term
import Fibril.Effect.Console
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.StringLiteral
import Fibril.Driver.Check
import Fibril.Driver.Console
import Fibril.Driver.Evaluate

%default total

hello : String
hello = "main : IO Unit\nmain = putStrLn \"Hello, world!\""

planned : String -> Maybe (List String)
planned source = case resolveSource source of
  Left _ => Nothing
  Right term => case prepareIO 128 128 term of
    Left _ => Nothing
    Right actions => Just (map (\(PrintLine value) => value) actions)

rejects : String -> Bool
rejects source = case checkSource False source of
  Left _ => True
  Right _ => False

public export
checks : List (String, Bool)
checks =
  [ ("console hello is a checked ordinary IO program",
      planned hello == Just ["Hello, world!"])
  , ("console check uses ordinary runtime typing",
      case checkSource False hello of
        Right lines => elem "Runtime checking: accepted" lines && elem "Type: (IO Unit)" lines
        Left _ => False)
  , ("console erased checking describes IO but performs nothing",
      case checkSource True hello of
        Right lines => elem "Type: (IO Unit)" lines
        Left _ => False)
  , ("console reference evaluation returns a description",
      case evaluateSource 16 hello of
        Right lines => elem "Normal: (WriteLine \"Hello, world!\")" lines
        Left _ => False)
  , ("console putStrLn is not parser syntax",
      planned "putStrLn : Bool -> IO Unit\nputStrLn = \\(flag : Bool) => pure Unit ()\nmain : IO Unit\nmain = putStrLn True" == Just [])
  , ("console normal helpers work",
      planned "say : (1 x : String) -> IO Unit\nsay = \\(1 x : String) => putStrLn x\nmain : IO Unit\nmain = say \"helper\"" == Just ["helper"])
  , ("console wrong type rejected", rejects "main : IO Bool\nmain = putStrLn \"bad\"")
  , ("console multiple literal arguments rejected", rejects (hello ++ " \"second\""))
  , ("console unknown function rejected", rejects "main : IO Unit\nmain = unknown \"bad\"")
  , ("console literal decode retains exact data",
      planned "main : IO Unit\nmain = putStrLn \"λ 🌍\\nquote: \\\"\"" == Just ["λ 🌍\nquote: \""])
  , ("strings token preserves spelling",
      case lexSource "\"a\\n\\\"\\\\b\"" of
        Right [token] => token.kind == StringToken && token.spelling == "\"a\\n\\\"\\\\b\""
        _ => False)
  , ("strings decode escapes without consuming suffix",
      case scanLiteral (At 0 1 1) (unpack "\"a\\n\\\"\\\\b\" tail") of
        Right literal => literal.value == "a\n\"\\b" && pack literal.remaining == " tail"
        Left _ => False)
  , ("strings unknown escape located",
      case lexSource "\"x\\q\"" of
        Left (BadString err) => err.position.column == 3
        _ => False)
  , ("strings unterminated EOF located",
      case lexSource "\"oops" of
        Left (BadString err) => err.position.column == 6
        _ => False)
  , ("strings raw newline rejected",
      case lexSource "\"x\nx\"" of
        Left (BadString _) => True
        _ => False)
  , ("strings raw tab rejected",
      case lexSource "\"x\tx\"" of
        Left (BadString _) => True
        _ => False)
  , ("strings source-wide policy retained",
      case lexSource ("\"" ++ pack [chr 0x202E] ++ "\"") of
        Left (InvalidSource _) => True
        _ => False)
  ]
