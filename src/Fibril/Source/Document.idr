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
  publicMarker : Maybe Token
  alias : Maybe Token
  selectors : Maybe (List Token)

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

||| Syntax-only clients must not report the internal framing of proof metadata
||| as ordinary values, or offer incomplete proof-reference rename previews.
public export
rejectCubicalMetadataInspection : ParsedDocument -> Either DocumentError ()
rejectCubicalMetadataInspection document = case document.body of
  DeclarationDocument authored => case find hasPathMetadata authored of
    Just (Ordinary decl) => Left (SymbolParsing (ParseFailure decl.nameSpan.start
      "Cubical metadata inspection is unsupported; use check (format preserves metadata)"))
    _ => Right ()
  _ => Right ()

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
  Right (names, Between keyword.span.start nameSpan.finish, nameSpan, rest)

parseSelectors : Nat -> Nat -> Position -> List Token -> Either ParseError (List Token, SourceSpan, List Token)
parseSelectors Z line end tokens = Left (ParseFailure (maybe end (\token => token.span.start) (head' tokens)) "Import selector budget exhausted (64)")
parseSelectors (S budget) line end [] = Left (ParseFailure end "Expected import selector")
parseSelectors (S budget) line end (token :: rest) = do
  if token.span.start.line /= line || token.kind /= Name || token.spelling == "_"
    then Left (ParseFailure token.span.start "Expected unqualified import selector on the import line") else Right ()
  case rest of
    separator :: following =>
      if separator.span.start.line /= line then Left (ParseFailure separator.span.start "Expected comma or closing parenthesis on the import line")
      else if separator.kind == CloseParen then Right ([token], separator.span, following)
      else if separator.kind == Comma then do
        (remaining, close, trailing) <- parseSelectors budget line end following
        Right (token :: remaining, close, trailing)
      else Left (ParseFailure separator.span.start "Expected comma or closing parenthesis")
    [] => Left (ParseFailure end "Expected closing parenthesis")

importHeaders : Nat -> Position -> List (List String) -> List Token ->
                Either ParseError (List ImportDeclaration, List Token)
importHeaders budget end seen [] = Right ([], [])
importHeaders budget end seen tokens@(token :: rest) =
  if token.kind /= ImportKeyword then Right ([], tokens) else
    case budget of
      Z => Left (ParseFailure token.span.start "Import count budget exhausted")
      S remaining => do
        let (publicMarker, afterPublic) = the (Maybe Token, List Token) $ case rest of
              marker :: following => if marker.spelling == "public" && marker.span.start.line == token.span.start.line
                then (Just marker, following) else (Nothing, rest)
              [] => (Nothing, rest)
        (names, span, nameSpan, afterName) <- header token end afterPublic
        (alias, following) <- the (Either ParseError (Maybe Token, List Token)) $ case afterName of
          marker :: value :: remaining =>
            if marker.span.start.line == token.span.start.line && marker.spelling == "as" then
              if value.span.start.line == token.span.start.line && component value.spelling
                 then Right (Just value, remaining)
                 else Left (ParseFailure value.span.start "Expected uppercase alias on the import line")
            else Right (Nothing, afterName)
          _ => Right (Nothing, afterName)
        (selection, importSpan, following) <- the (Either ParseError (Maybe (List Token), SourceSpan, List Token)) $ case following of
          opening :: trailing => if opening.kind == OpenParen && opening.span.start.line == token.span.start.line then do
            (names, close, trailing) <- parseSelectors 64 token.span.start.line end trailing
            Right (Just names, Between span.start close.finish, trailing)
            else Right (Nothing, maybe span (\value => Between span.start value.span.finish) alias, following)
          [] => Right (Nothing, maybe span (\value => Between span.start value.span.finish) alias, following)
        if isJust publicMarker && isNothing selection
          then Left (ParseFailure token.span.start "Public import requires a nonempty selector") else Right ()
        case following of
          next :: _ => if next.span.start.line == token.span.start.line
            then Left (ParseFailure next.span.start "Unexpected tokens after import header") else Right ()
          [] => Right ()
        if elem names seen then Left (ParseFailure token.span.start "Duplicate direct import")
           else Right ()
        (imports, trailing) <- importHeaders remaining end (names :: seen) following
        Right (Imported importSpan nameSpan names publicMarker alias selection :: imports, trailing)

validateAliases : Maybe ModuleHeader -> List ImportDeclaration -> Either ParseError ()
validateAliases header imports = check [] imports
  where
    prefixes : List String
    prefixes = mapMaybe (head' . components) imports ++
               maybe [] (\h => maybe [] pure (head' h.components)) header

    check : List String -> List ImportDeclaration -> Either ParseError ()
    check seen [] = Right ()
    check seen (dependency :: rest) = case dependency.alias of
      Nothing => check seen rest
      Just alias =>
        if elem alias.spelling seen || elem alias.spelling prefixes
          then Left (ParseFailure alias.span.start "Import alias conflicts with another alias or module qualifier prefix")
          else check (alias.spelling :: seen) rest

parseTokens : Nat -> Nat -> Position -> List Token -> Either ParseError ParsedDocument
parseTokens declarations expressions end tokens = do
  (moduleHeader, following) <- the (Either ParseError (Maybe ModuleHeader, List Token)) $
    case tokens of
      token :: rest => if token.kind == ModuleKeyword then do
        (names, span, nameSpan, following) <- header token end rest
        case following of
          next :: _ => if next.span.start.line == token.span.start.line
            then Left (ParseFailure next.span.start "Unexpected tokens after module header") else Right ()
          [] => Right ()
        Right (Just (Header span nameSpan names), following)
        else Right (Nothing, tokens)
      [] => Right (Nothing, [])
  (imports, remaining) <- importHeaders 32 end [] following
  validateAliases moduleHeader imports
  if isNothing moduleHeader && any (isJust . publicMarker) imports
    then Left (ParseFailure (maybe end (\dependency => dependency.span.start) (find (isJust . publicMarker) imports)) "Public imports require a named module") else Right ()
  body <- the (Either ParseError DocumentBody) $ case remaining of
    [] => Right EmptyDocument
    first :: _ =>
      if isJust moduleHeader || declarationAhead remaining then do
        values <- parseAuthoredDeclarations declarations expressions end remaining
        if isNothing moduleHeader && any requiresElaboration values
           then Left (ParseFailure first.span.start "Data/record/interface/implementation declarations require a named module")
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
