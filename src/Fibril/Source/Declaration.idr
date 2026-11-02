-- Grammar and authored declaration framing. Record lowering is a separate pass.
module Fibril.Source.Declaration

import Data.List
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Parser
import public Fibril.Source.Declaration.Syntax

%default total

nextPosition : Position -> List Token -> Position
nextPosition end [] = end
nextPosition end (token :: _) = token.span.start

-- The header's remaining tokens and later indented lines form one expression.
-- A later column-one token always starts the next declaration frame.
expressionChunk : Nat -> List Token -> (List Token, List Token)
expressionChunk headerLine =
  span (\token => token.span.start.line == headerLine || token.span.start.column > 1)

parsePair : Nat -> Position -> List Token ->
           Either ParseError (Declaration, List Token)
parsePair expressionBudget end [] = Left (ParseFailure end "Expected declaration signature")
parsePair expressionBudget end tokens@(first :: _) = do
  if first.span.start.column /= 1
     then Left (ParseFailure first.span.start "Declaration headers must start in column 1")
     else Right ()
  (q, afterQuantity) <- binderQuantity tokens
  (name, afterName) <- expect Name end afterQuantity
  (colon, afterColon) <- expect Colon end afterName
  if name.span.start.line /= first.span.start.line ||
     colon.span.start.line /= first.span.start.line
     then Left (ParseFailure name.span.start "Signature name and colon must share the header line")
     else Right ()
  let (typeTokens, afterType) = expressionChunk first.span.start.line afterColon
  expected <- parseExpression expressionBudget (nextPosition end afterType) typeTokens
  (definedName, afterDefinedName) <- expect Name end afterType
  if definedName.span.start.column /= 1
     then Left (ParseFailure definedName.span.start "Definition headers must start in column 1")
     else Right ()
  if definedName.spelling /= name.spelling
     then Left (ParseFailure definedName.span.start
                ("Expected definition of " ++ show name.spelling ++
                 ", found " ++ show definedName.spelling))
     else Right ()
  (equals, afterEquals) <- expect Equals end afterDefinedName
  if equals.span.start.line /= definedName.span.start.line
     then Left (ParseFailure equals.span.start "Definition name and = must share the header line")
     else Right ()
  let (valueTokens, remaining) = expressionChunk definedName.span.start.line afterEquals
  value <- parseExpression expressionBudget (nextPosition end remaining) valueTokens
  Right (Defined (Between first.span.start (extent value).finish)
                 name.span definedName.span False q name.spelling expected value, remaining)


directive : TokenKind -> Nat -> Position -> List Token ->
            Either ParseError (Token, Token, List Token)
directive kind indent end tokens = do
  (keyword, rest) <- expect kind end tokens
  (name, remaining) <- expect Name end rest
  if keyword.span.start.column /= indent || indent <= 1 ||
     name.span.start.line /= keyword.span.start.line || name.spelling == "_" ||
     (case remaining of next :: _ => next.span.start.line == keyword.span.start.line; [] => False)
     then Left (ParseFailure keyword.span.start "Record directives need their own aligned indented line and a name")
     else Right (keyword, name, remaining)

parseField : Nat -> Nat -> Position -> List Token -> Either ParseError (RecordField, List Token)
parseField budget indent end [] = Left (ParseFailure end "Expected record field")
parseField budget indent end tokens@(first :: _) = do
  if first.span.start.column /= indent
     then Left (ParseFailure first.span.start "Record fields must align with constructor/eliminator")
     else Right ()
  let (line, remaining) = span (\token => token.span.start.line == first.span.start.line) tokens
  (q, following) <- binderQuantity line
  (name, following) <- expect Name end following
  (_, following) <- expect Colon end following
  ty <- parseExpression budget (nextPosition end remaining) following
  Right (Field name q ty, remaining)

parseProjections : Nat -> Nat -> Position -> List Token ->
                   Either ParseError (List RecordProjection, List Token)
parseProjections fuel indent end tokens = case tokens of
  token :: rest => if token.kind /= ProjectionKeyword then Right ([], tokens) else
    case fuel of
      Z => Left (ParseFailure token.span.start "Record projection budget exhausted (2)")
      S fuel => do
        (name, rest) <- expect Name end rest
        (field, rest) <- expect Name end rest
        if token.span.start.column /= indent || name.spelling == "_" ||
           field.span.start.line /= token.span.start.line ||
           (case rest of next :: _ => next.span.start.line == token.span.start.line; [] => False)
           then Left (ParseFailure token.span.start "Expected aligned projection getter field on its own line")
           else Right ()
        (following, remaining) <- parseProjections fuel indent end rest
        Right (Projected token name field :: following, remaining)
  [] => Right ([], [])

recordParameters : Nat -> Nat -> Position -> List Token ->
                   Either ParseError (List RecordParameter, List Token)
recordParameters fuel expressions end tokens = case tokens of
  token :: _ => if token.kind /= OpenParen then Right ([], tokens) else
    case fuel of
      Z => Left (ParseFailure token.span.start "Record parameter budget exhausted (8)")
      S fuel => do
        parameter <- binder expressions end tokens
        (rest, remaining) <- recordParameters fuel expressions end parameter.remaining
        Right (Parameter parameter.span parameter.quantity parameter.name parameter.domain :: rest, remaining)
  [] => Right ([], [])

parseRecord : Nat -> Position -> List Token -> Either ParseError (AuthoredDeclaration, List Token)
parseRecord budget end tokens = do
  (keyword, rest) <- expect RecordKeyword end tokens
  (name, rest) <- expect Name end rest
  (params, rest) <- recordParameters 8 budget end rest
  (_, rest) <- expect Colon end rest
  (_, rest) <- expect TypeKeyword end rest
  (universe, rest) <- expect Number end rest
  level <- levelValue universe
  (whereToken, rest) <- expect WhereKeyword end rest
  if keyword.span.start.column /= 1 || name.spelling == "_" ||
     whereToken.span.start.line /= keyword.span.start.line
     then Left (ParseFailure keyword.span.start "Expected a single-line, column-one record header ending : Type n where")
     else Right ()
  let indent = case rest of token :: _ => token.span.start.column; [] => 0
  (constructorKeyword, constructorName, rest) <- directive ConstructorKeyword indent end rest
  if constructorKeyword.span.start.line <= whereToken.span.start.line
     then Left (ParseFailure constructorKeyword.span.start "constructor must follow the record header")
     else Right ()
  (eliminatorKeyword, eliminatorName, rest) <- directive EliminatorKeyword indent end rest
  (first, rest) <- parseField budget indent end rest
  (second, rest) <- parseField budget indent end rest
  (projections, rest) <- parseProjections 2 indent end rest
  case rest of
    token :: _ => if token.span.start.column > 1
                    then Left (ParseFailure token.span.start "Prototype records require exactly two single-line fields followed by optional projections")
                    else Right ()
    [] => Right ()
  let finish = case reverse projections of
        [] => (extent second.ty).finish
        final :: _ => final.field.span.finish
  let region = Between keyword.span.start finish
  Right (RecordItem (RecordSyntax region name level params constructorKeyword constructorName eliminatorKeyword eliminatorName first second projections False), rest)


parseOne : Nat -> Position -> List Token -> Either ParseError (AuthoredDeclaration, List Token)
parseOne budget end tokens@(token :: rest) =
  if token.kind == ExportKeyword then do
    if token.span.start.column /= 1
       then Left (ParseFailure token.span.start "export must start in column 1") else Right ()
    case rest of
      next :: _ => if next.kind == ExportKeyword then Left (ParseFailure next.span.start "Duplicate export marker") else Right ()
      [] => Right ()
    (item, remaining) <- parseOne budget end rest
    let start = case item of
          Ordinary decl => decl.span.start
          RecordItem sourceRecord => sourceRecord.span.start
    if start.line <= token.span.start.line
       then Left (ParseFailure start "export must precede the declaration on its own line") else Right ()
    let marked = case item of
          Ordinary decl => Ordinary ({ exported := True, span := Between token.span.start decl.span.finish } decl)
          RecordItem sourceRecord => RecordItem ({ exported := True, span := Between token.span.start sourceRecord.span.finish } sourceRecord)
    Right (marked, remaining)
  else if token.kind == RecordKeyword then parseRecord budget end tokens
  else do
    (decl, remaining) <- parsePair budget end tokens
    Right (Ordinary decl, remaining)
parseOne budget end [] = Left (ParseFailure end "Expected declaration")

admit : Nat -> List String -> List BindingSite -> Either ParseError (Nat, List String)
admit slots seen [] = Right (slots, seen)
admit Z seen (site :: _) = Left (ParseFailure site.nameSpan.start "Declaration count budget exhausted")
admit (S slots) seen (site :: rest) =
  if elem site.name seen then Left (ParseFailure site.nameSpan.start ("Duplicate declaration " ++ show site.name))
     else admit slots (site.name :: seen) rest

parseAll : Nat -> Nat -> Nat -> Position -> List String -> List Token ->
           Either ParseError (List AuthoredDeclaration)
parseAll fuel slots expressions end seen [] = Right []
parseAll Z slots expressions end seen tokens =
  Left (ParseFailure (nextPosition end tokens) "Declaration count budget exhausted")
parseAll (S fuel) slots expressions end seen tokens = do
  (item, remaining) <- parseOne expressions end tokens
  (slots, seen) <- admit slots seen (bindingSites item)
  rest <- parseAll fuel slots expressions end seen remaining
  Right (item :: rest)

||| Parse authored syntax only. Binding-site quotas do not generate definitions.
public export
parseAuthoredDeclarations : Nat -> Nat -> Position -> List Token ->
                            Either ParseError (List AuthoredDeclaration)
parseAuthoredDeclarations budget expressions end = parseAll budget budget expressions end []

||| Legacy ordinary-only adapter. Records require explicit authored parsing and
||| the separate elaborator; this grammar module has no elaborator dependency.
public export
parseDeclarations : Nat -> Nat -> Position -> List Token -> Either ParseError (List Declaration)
parseDeclarations budget expressions end tokens = do
  authored <- parseAuthoredDeclarations budget expressions end tokens
  if any isRecord authored then Left (ParseFailure end "Records require the authored document/elaboration pipeline")
     else Right (ordinaryDeclarations authored)

-- Synthetic entry reference is at EOF; all lowered let extents stay ordered.
-- Presence of main is checked before lowering; no source location is invented
-- for a core typing error or for a nonexistent entry.
legacyLowerDeclarations : Position -> List Declaration -> Expr
legacyLowerDeclarations end [] = NRef (Between end end) "main"
legacyLowerDeclarations end (decl :: rest) =
  NLet (Between decl.span.start end) decl.quantity decl.name decl.expected decl.value
       (legacyLowerDeclarations end rest)

public export
declarationAhead : List Token -> Bool
declarationAhead (Located Name _ _ :: Located Colon _ _ :: _) = True
declarationAhead (Located Name _ _ :: Located Equals _ _ :: _) = True
declarationAhead (Located Number _ _ :: _) = True
declarationAhead (Located RecordKeyword _ _ :: _) = True
declarationAhead (Located ExportKeyword _ _ :: _) = True
declarationAhead _ = False

||| Accept an expression or a nonrecursive declaration file with fixed main entry.
||| Declarations elaborate to existing typed lets; no new trusted core rule.
public export
parseSource : (declarationBudget, expressionBudget : Nat) -> Position ->
              List Token -> Either ParseError Expr
parseSource declarationBudget expressionBudget end tokens =
  if declarationAhead tokens then do
    declarations <- parseDeclarations declarationBudget expressionBudget end tokens
    if any generated declarations then Left (ParseFailure end "Records require a named module; use parseDocument") else Right ()
    if any (\decl => decl.exported) declarations
       then Left (ParseFailure end "export requires a named module; use parseDocument")
       else Right ()
    if any (\decl => decl.name == "main") declarations
       then Right (legacyLowerDeclarations end declarations)
       else Left (ParseFailure end "Declaration file requires a main definition")
  else parseExpression expressionBudget end tokens
