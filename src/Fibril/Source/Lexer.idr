-- Minimal expression tokens, not the complete Idris-like surface language.
module Fibril.Source.Lexer

import Data.List
import Fibril.Source.Text

%default total

||| Token categories for the initial explicitly annotated expression grammar.
public export
data TokenKind = Name | Number | TypeKeyword | OpenParen | CloseParen | Colon | Arrow | BodyArrow | Lambda

public export
Show TokenKind where
  show Name = "name"
  show Number = "number"
  show TypeKeyword = "Type"
  show OpenParen = "("
  show CloseParen = ")"
  show Colon = ":"
  show Arrow = "->"
  show BodyArrow = "=>"
  show Lambda = "lambda"

public export
Eq TokenKind where
  Name == Name = True
  Number == Number = True
  TypeKeyword == TypeKeyword = True
  OpenParen == OpenParen = True
  CloseParen == CloseParen = True
  Colon == Colon = True
  Arrow == Arrow = True
  BodyArrow == BodyArrow = True
  Lambda == Lambda = True
  _ == _ = False

||| Half-open scalar positions. These are not byte offsets or UTF-16 indices.
public export
record SourceSpan where
  constructor Between
  start : Position
  finish : Position

||| Keep original spelling for diagnostics, including Unicode aliases.
public export
record Token where
  constructor Located
  kind : TokenKind
  spelling : String
  span : SourceSpan

public export
Show Token where
  show token = show token.span.start ++ "-" ++ show token.span.finish ++
               " " ++ show token.kind ++ " " ++ show token.spelling

||| Distinguish text-policy errors from lexically unsupported characters.
public export
data LexError = InvalidSource TextError | UnexpectedChar Position Char | ScanLimit

public export
Show LexError where
  show (InvalidSource err) = show err
  show (UnexpectedChar at char) = show at ++ ": Unexpected character " ++ show char
  show ScanLimit = "Internal lexer progress budget exhausted"

asciiLetter : Char -> Bool
asciiLetter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

digit : Char -> Bool
digit c = c >= '0' && c <= '9'

nameStart : Char -> Bool
nameStart c = asciiLetter c || c == '_'

nameRest : Char -> Bool
nameRest c = nameStart c || digit c || c == '\''

whitespace : Char -> Bool
whitespace c = c == ' ' || c == '\t' || c == '\n' || c == '\r'

emit : Position -> TokenKind -> List Char -> Token
emit at kind chars =
  Located kind (pack chars) (Between at (advancePosition at chars))

-- Fuel is bounded by input scalar length. Each recursive call consumes at
-- least one scalar, including whitespace/comments; span/drop are not filters
-- on arbitrary untrusted recursion. This is not a time/memory guarantee.
scan : Nat -> Position -> List Char -> Either LexError (List Token)
scan fuel at [] = Right []
scan Z at (_ :: _) = Left ScanLimit
scan (S fuel) at ('-' :: '-' :: rest) =
  let (comment, remaining) = span (\c => c /= '\n' && c /= '\r') rest
   in scan fuel (advancePosition at ('-' :: '-' :: comment)) remaining
scan (S fuel) at ('-' :: '>' :: rest) = do
  let token = emit at Arrow ['-', '>']
  tokens <- scan fuel token.span.finish rest
  Right (token :: tokens)
scan (S fuel) at ('=' :: '>' :: rest) = do
  let token = emit at BodyArrow ['=', '>']
  tokens <- scan fuel token.span.finish rest
  Right (token :: tokens)
scan (S fuel) at (c :: rest) =
  if whitespace c
     then let (spaces, remaining) = span whitespace rest
           in scan fuel (advancePosition at (c :: spaces)) remaining
  else if nameStart c
     then do
       let (suffix, remaining) = span nameRest rest
       let chars = c :: suffix
       let kind = if pack chars == "Type" then TypeKeyword else Name
       let token = emit at kind chars
       tokens <- scan fuel token.span.finish remaining
       Right (token :: tokens)
  else if digit c
     then do
       let (suffix, remaining) = span digit rest
       let token = emit at Number (c :: suffix)
       tokens <- scan fuel token.span.finish remaining
       Right (token :: tokens)
  else do
    kind <- case c of
      '(' => Right OpenParen
      ')' => Right CloseParen
      ':' => Right Colon
      '\\' => Right Lambda
      'λ' => Right Lambda
      '→' => Right Arrow
      '⇒' => Right BodyArrow
      _ => Left (UnexpectedChar at c)
    let token = emit at kind [c]
    tokens <- scan fuel token.span.finish rest
    Right (token :: tokens)

||| Validate decoded text then lex the initial expression subset.
||| Only ASCII identifiers are accepted until a versioned Unicode policy exists.
||| Comments/whitespace are skipped; no indentation/layout tokens exist yet.
||| Numbers retain digit spelling and are not converted to machine integers.
public export
lexSource : String -> Either LexError (List Token)
lexSource source = do
  case validateText source of
    Left err => Left (InvalidSource err)
    Right _ => Right ()
  let chars = unpack source
  scan (length chars) (At 0 1 1) chars
