-- Minimal expression tokens, not the complete Idris-like surface language.
module Fibril.Source.Lexer

import Data.List
import Fibril.Source.Text
import Fibril.Source.StringLiteral

%default total

||| Token categories for the initial explicitly annotated expression grammar.
public export
data TokenKind = Name | Number | StringToken | StringKeyword | TypeKeyword | UnitKeyword | BoolKeyword | TrueKeyword | FalseKeyword | IfKeyword | ThenKeyword | ElseKeyword | DoKeyword | CaseKeyword | OfKeyword | LetKeyword | InKeyword | ProjectionKeyword | ReturnKeyword | DataKeyword | RecordKeyword | InterfaceKeyword | ImplementationKeyword | ConstructorKeyword | EliminatorKeyword | WhereKeyword | ModuleKeyword | ImportKeyword | ExportKeyword | Dot | Equals | OpenParen | CloseParen | OpenBrace | DictionaryOpen | CloseBrace | Backtick | Colon | Arrow | BindArrow | BodyArrow | Lambda

public export
Show TokenKind where
  show Name = "name"
  show Number = "number"
  show StringToken = "string"
  show StringKeyword = "String"
  show TypeKeyword = "Type"
  show UnitKeyword = "Unit"
  show BoolKeyword = "Bool"
  show TrueKeyword = "True"
  show FalseKeyword = "False"
  show IfKeyword = "if"
  show ThenKeyword = "then"
  show ElseKeyword = "else"
  show DoKeyword = "do"
  show CaseKeyword = "case"
  show OfKeyword = "of"
  show LetKeyword = "let"
  show InKeyword = "in"
  show ProjectionKeyword = "projection"
  show ReturnKeyword = "return"
  show DataKeyword = "data"
  show RecordKeyword = "record"
  show InterfaceKeyword = "interface"
  show ImplementationKeyword = "implementation"
  show ConstructorKeyword = "constructor"
  show EliminatorKeyword = "eliminator"
  show WhereKeyword = "where"
  show ModuleKeyword = "module"
  show ImportKeyword = "import"
  show ExportKeyword = "export"
  show Dot = "."
  show Equals = "="
  show Backtick = "`"
  show OpenBrace = "{"
  show DictionaryOpen = "@{"
  show CloseBrace = "}"
  show OpenParen = "("
  show CloseParen = ")"
  show Colon = ":"
  show Arrow = "->"
  show BindArrow = "<-"
  show BodyArrow = "=>"
  show Lambda = "lambda"

public export
Eq TokenKind where
  Name == Name = True
  Number == Number = True
  StringToken == StringToken = True
  StringKeyword == StringKeyword = True
  TypeKeyword == TypeKeyword = True
  UnitKeyword == UnitKeyword = True
  BoolKeyword == BoolKeyword = True
  TrueKeyword == TrueKeyword = True
  FalseKeyword == FalseKeyword = True
  IfKeyword == IfKeyword = True
  ThenKeyword == ThenKeyword = True
  ElseKeyword == ElseKeyword = True
  DoKeyword == DoKeyword = True
  CaseKeyword == CaseKeyword = True
  OfKeyword == OfKeyword = True
  LetKeyword == LetKeyword = True
  InKeyword == InKeyword = True
  ProjectionKeyword == ProjectionKeyword = True
  ReturnKeyword == ReturnKeyword = True
  DataKeyword == DataKeyword = True
  RecordKeyword == RecordKeyword = True
  InterfaceKeyword == InterfaceKeyword = True
  ImplementationKeyword == ImplementationKeyword = True
  ConstructorKeyword == ConstructorKeyword = True
  EliminatorKeyword == EliminatorKeyword = True
  WhereKeyword == WhereKeyword = True
  ModuleKeyword == ModuleKeyword = True
  ImportKeyword == ImportKeyword = True
  ExportKeyword == ExportKeyword = True
  Dot == Dot = True
  Equals == Equals = True
  Backtick == Backtick = True
  OpenBrace == OpenBrace = True
  DictionaryOpen == DictionaryOpen = True
  CloseBrace == CloseBrace = True
  OpenParen == OpenParen = True
  CloseParen == CloseParen = True
  Colon == Colon = True
  Arrow == Arrow = True
  BindArrow == BindArrow = True
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
data LexError = InvalidSource TextError | UnexpectedChar Position Char | BadString LiteralError | ScanLimit

public export
Show LexError where
  show (InvalidSource err) = show err
  show (UnexpectedChar at char) = show at ++ ": Unexpected character " ++ show char
  show (BadString err) = show err
  show ScanLimit = "Internal lexer progress budget exhausted"

asciiLetter : Char -> Bool
asciiLetter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

digit : Char -> Bool
digit c = c >= '0' && c <= '9'

nameStart : Char -> Bool
nameStart c = asciiLetter c || c == '_'

||| Shared module-qualifier spelling; keywords such as String are valid components.
public export
validModuleComponent : String -> Bool
validModuleComponent text = case unpack text of
  [] => False
  first :: rest => first >= 'A' && first <= 'Z' &&
    all (\c => (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
               (c >= '0' && c <= '9') || c == '_') rest

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
scan (S fuel) at chars@('"' :: _) = do
  literal <- case scanLiteral at chars of
    Left err => Left (BadString err)
    Right literal => Right literal
  let token = emit at StringToken literal.original
  tokens <- scan fuel token.span.finish literal.remaining
  Right (token :: tokens)
scan (S fuel) at ('-' :: '-' :: rest) =
  let (comment, remaining) = span (\c => c /= '\n' && c /= '\r') rest
   in scan fuel (advancePosition at ('-' :: '-' :: comment)) remaining
scan (S fuel) at ('-' :: '>' :: rest) = do
  let token = emit at Arrow ['-', '>']
  tokens <- scan fuel token.span.finish rest
  Right (token :: tokens)
scan (S fuel) at ('<' :: '-' :: rest) = do
  let token = emit at BindArrow ['<', '-']
  tokens <- scan fuel token.span.finish rest
  Right (token :: tokens)
scan (S fuel) at ('=' :: '>' :: rest) = do
  let token = emit at BodyArrow ['=', '>']
  tokens <- scan fuel token.span.finish rest
  Right (token :: tokens)
scan (S fuel) at ('@' :: '{' :: rest) = do
  let token = emit at DictionaryOpen ['@', '{']
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
       let kind = case pack chars of
             "String" => StringKeyword
             "Type" => TypeKeyword
             "Unit" => UnitKeyword
             "Bool" => BoolKeyword
             "True" => TrueKeyword
             "False" => FalseKeyword
             "if" => IfKeyword
             "then" => ThenKeyword
             "else" => ElseKeyword
             "do" => DoKeyword
             "case" => CaseKeyword
             "of" => OfKeyword
             "let" => LetKeyword
             "in" => InKeyword
             "projection" => ProjectionKeyword
             "return" => ReturnKeyword
             "data" => DataKeyword
             "record" => RecordKeyword
             "interface" => InterfaceKeyword
             "implementation" => ImplementationKeyword
             "constructor" => ConstructorKeyword
             "eliminator" => EliminatorKeyword
             "where" => WhereKeyword
             "module" => ModuleKeyword
             "import" => ImportKeyword
             "export" => ExportKeyword
             _ => Name
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
      '`' => Right Backtick
      '.' => Right Dot
      '(' => Right OpenParen
      ')' => Right CloseParen
      '{' => Right OpenBrace
      '}' => Right CloseBrace
      ':' => Right Colon
      '=' => Right Equals
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
