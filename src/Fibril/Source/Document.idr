-- One syntax-only document parser for checking and editor services.
module Fibril.Source.Document

import Data.List
import Data.Maybe
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Parser
import Fibril.Source.Declaration

%default total

public export
data DocumentError = SymbolLexical LexError | SymbolParsing ParseError

public export
record ModuleHeader where
  constructor Header
  span : SourceSpan
  nameSpan : SourceSpan
  components : List String

public export
record ImportDeclaration where
  constructor Imported
  span : SourceSpan
  nameSpan : SourceSpan
  components : List String

public export
data DocumentBody = EmptyDocument | ExpressionDocument Expr | DeclarationDocument (List AuthoredDeclaration)

public export
record ParsedDocument where
  constructor Document
  moduleHeader : Maybe ModuleHeader
  imports : List ImportDeclaration
  tokens : List Token
  end : Position
  body : DocumentBody

component : String -> Bool
component = validModuleComponent

parts : Nat -> Position -> Nat -> List Token ->
        Either ParseError (List String, SourceSpan, List Token)
parts Z end line [] = Left (ParseFailure end "Module name component budget exhausted")
parts Z end line (token :: _) = Left (ParseFailure token.span.start "Module name component budget exhausted")
parts (S budget) end line [] = Left (ParseFailure end "Expected module name component")
parts (S budget) end line (token :: rest) = do
  if token.span.start.line /= line || not (component token.spelling)
     then Left (ParseFailure token.span.start "Expected uppercase ASCII module component on the header line")
     else Right ()
  case rest of
    dot :: following =>
      if dot.kind == Dot && dot.span.start.line == line then do
        (names, span, remaining) <- parts budget end line following
        Right (token.spelling :: names, Between token.span.start span.finish, remaining)
      else Right ([token.spelling], token.span, rest)
    [] => Right ([token.spelling], token.span, [])

header : Token -> Position -> List Token ->
         Either ParseError (List String, SourceSpan, SourceSpan, List Token)
header keyword end tokens = do
  if keyword.span.start.column /= 1
     then Left (ParseFailure keyword.span.start "Module/import headers must start in column 1")
     else Right ()
  (names, nameSpan, rest) <- parts 16 end keyword.span.start.line tokens
  case rest of
    token :: _ => if token.span.start.line == keyword.span.start.line
      then Left (ParseFailure token.span.start "Unexpected tokens after module/import header")
      else Right ()
    [] => Right ()
  Right (names, Between keyword.span.start nameSpan.finish, nameSpan, rest)

importHeaders : Nat -> Position -> List (List String) -> List Token ->
                Either ParseError (List ImportDeclaration, List Token)
importHeaders budget end seen [] = Right ([], [])
importHeaders budget end seen tokens@(token :: rest) =
  if token.kind /= ImportKeyword then Right ([], tokens) else
    case budget of
      Z => Left (ParseFailure token.span.start "Import count budget exhausted")
      S remaining => do
        (names, span, nameSpan, following) <- header token end rest
        if elem names seen then Left (ParseFailure token.span.start "Duplicate direct import")
           else Right ()
        (imports, trailing) <- importHeaders remaining end (names :: seen) following
        Right (Imported span nameSpan names :: imports, trailing)

parseTokens : Nat -> Nat -> Position -> List Token -> Either ParseError ParsedDocument
parseTokens declarations expressions end tokens = do
  (moduleHeader, following) <- the (Either ParseError (Maybe ModuleHeader, List Token)) $
    case tokens of
      token :: rest => if token.kind == ModuleKeyword then do
        (names, span, nameSpan, following) <- header token end rest
        Right (Just (Header span nameSpan names), following)
        else Right (Nothing, tokens)
      [] => Right (Nothing, [])
  (imports, remaining) <- importHeaders 32 end [] following
  body <- the (Either ParseError DocumentBody) $ case remaining of
    [] => Right EmptyDocument
    first :: _ =>
      if isJust moduleHeader || declarationAhead remaining then do
        values <- parseAuthoredDeclarations declarations expressions end remaining
        if isNothing moduleHeader && any isRecord values
           then Left (ParseFailure first.span.start "Record declarations require a named module")
           else Right ()
        if isNothing moduleHeader && any declarationExported values
           then Left (ParseFailure first.span.start "export requires a named module")
           else Right (DeclarationDocument values)
      else ExpressionDocument <$> parseExpression expressions end remaining
  Right (Document moduleHeader imports tokens end body)

||| No main requirement or module identity/loading claim. Header limits: 16 name
||| components and 32 direct imports. Expression/declaration budgets are independent.
public export
parseDocument : Nat -> Nat -> String -> Either DocumentError ParsedDocument
parseDocument declarations expressions source = do
  tokens <- case lexSource source of
    Left err => Left (SymbolLexical err)
    Right tokens => Right tokens
  case parseTokens declarations expressions (advancePosition (At 0 1 1) (unpack source)) tokens of
    Left err => Left (SymbolParsing err)
    Right document => Right document
