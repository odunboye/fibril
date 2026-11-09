module Tests.Lexer

import Data.List
import Fibril.Source.Text
import Fibril.Source.Lexer

%default total

spellings : String -> List String -> Bool
spellings source expected =
  case lexSource source of
    Right tokens => map spelling tokens == expected
    Left _ => False

kinds : String -> List String -> Bool
kinds source expected =
  case lexSource source of
    Right tokens => map (show . kind) tokens == expected
    Left _ => False

||| Minimal tokenization tests; no parser or Unicode identifier approval implied.
public export
checks : List (String, Bool)
checks =
  [ ("lexer String keyword exact", kinds "String StringValue string" ["String", "name", "name"])
  , ("lexer Boolean keywords exact", kinds "Bool True False if then else iffy" ["Bool", "True", "False", "if", "then", "else", "name"])
  , ("lexer case keywords exact", kinds "case of cases offset" ["case", "of", "name", "name"])
  , ("lexer Unit keyword is exact", kinds "Unit UnitValue unit" ["Unit", "name", "name"])
  , ("lexer let keywords are exact", kinds "let in letter inner =" ["let", "in", "name", "name", "="])
  , ("lexer empty", spellings "" [])
  , ("lexer whitespace", spellings " \t\r\n" [])
  , ("lexer annotated lambda",
      spellings "\\(1 x : Type 0) => x" ["\\", "(", "1", "x", ":", "Type", "0", ")", "=>", "x"])
  , ("lexer aliases agree",
      kinds "λ (x : A) ⇒ x → A" ["lambda", "(", "name", ":", "name", ")", "=>", "name", "->", "name"])
  , ("lexer retains Unicode spelling", spellings "λ x ⇒ x" ["λ", "x", "⇒", "x"])
  , ("lexer ASCII names", spellings "_value value2 x' Type0" ["_value", "value2", "x'", "Type0"])
  , ("lexer keyword is exact", kinds "Type Type0 type" ["Type", "name", "name"])
  , ("lexer number spelling", spellings "000123" ["000123"])
  , ("lexer comments", spellings "-- 🌊\r\nx -- done" ["x"])
  , ("lexer scalar/CRLF/tab span",
      case lexSource "x\r\n\t→" of
        Right [_, arrow] =>
          arrow.span.start.offset == 4 && arrow.span.start.line == 2 &&
          arrow.span.start.column == 2 && arrow.span.finish.offset == 5
        _ => False)
  , ("lexer astral comment position",
      case lexSource "-- 🌊\r\nx" of
        Right [token] => token.span.start.offset == 6 &&
                         token.span.start.line == 2 && token.span.start.column == 1
        _ => False)
  , ("lexer unsupported Unicode identifier",
      case lexSource "é" of
        Left (UnexpectedChar at 'é') => at.offset == 0
        _ => False)
  , ("lexer unsupported punctuation location",
      case lexSource "->;" of
        Left (UnexpectedChar at ';') => at.offset == 2
        _ => False)
  , ("lexer text policy precedes comments",
      case lexSource ("-- " ++ pack [chr 0x202E]) of
        Left (InvalidSource _) => True
        _ => False)
  , ("lexer symbol run is one operator token",
      case lexSource "a +-+ b" of
        Right [_, op, _] => op.kind == Operator && op.spelling == "+-+"
        _ => False)
  , ("lexer reserved runs keep their meaning",
      case lexSource "= | : -> => <-" of
        Right tokens => map (\t => t.kind) tokens == [Equals, Bar, Colon, Arrow, BodyArrow, BindArrow]
        _ => False)
  , ("lexer parenthesised operator is one name",
      case lexSource "(+)" of
        Right [name] => name.kind == Name && name.spelling == "+" && name.span.finish.offset == 3
        _ => False)
  , ("lexer spaced parenthesised operator stays separate",
      case lexSource "( + )" of
        Right tokens => length tokens == 3
        _ => False)
  ]
