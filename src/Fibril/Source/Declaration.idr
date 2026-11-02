-- Source-ordered declarations and bounded record expansion; no recursive bindings.
module Fibril.Source.Declaration

import Data.List
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Parser

%default total

||| An ordinary or record-derived declaration before resolution/type checking.
||| Generated bodies are checked normally but have no separate authored source spans.
public export
record Declaration where
  constructor Declared
  generated : Bool
  span : SourceSpan
  nameSpan : SourceSpan
  definitionNameSpan : SourceSpan
  exported : Bool
  quantity : Quantity
  name : String
  expected : Expr
  value : Expr

||| Ordinary source signature/definition pair (not record expansion).
public export
Defined : SourceSpan -> SourceSpan -> SourceSpan -> Bool -> Quantity -> String -> Expr -> Expr -> Declaration
Defined = Declared False

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


record ParsedField where
  constructor Field
  token : Token
  quantity : Quantity
  ty : Expr

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

parseField : Nat -> Nat -> Position -> List Token -> Either ParseError (ParsedField, List Token)
parseField budget indent end [] = Left (ParseFailure end "Expected record field")
parseField budget indent end tokens@(first :: _) = do
  if first.span.start.column /= indent
     then Left (ParseFailure first.span.start "Record fields must align with constructor/eliminator")
     else Right ()
  let (line, remaining) = span (\token => token.span.start.line == first.span.start.line) tokens
  (q, following) <- binderQuantity line
  (name, following) <- expect Name end following
  (_, following) <- expect Colon end following
  if name.spelling == "_" then Left (ParseFailure name.span.start "Record fields need referenceable names") else Right ()
  ty <- parseExpression budget (nextPosition end remaining) following
  Right (Field name q ty, remaining)

-- Generated binders cannot be captured by any legal source identifier.
-- Global-only references use the resolver's separate qualified namespace,
-- even for these unqualified generated declaration names.
recordDeclarations : SourceSpan -> Token -> Nat -> Token -> Token -> Token -> Token ->
                     ParsedField -> ParsedField -> List Declaration
recordDeclarations region name level constructorKeyword constructorName eliminatorKeyword eliminatorName first second =
  let typeRef = NQualifiedRef name.span name.spelling
      ctorRef = NQualifiedRef constructorName.span constructorName.spelling
      x = first.token.spelling
      y = second.token.spelling
      xRef = NRef first.token.span x
      yRef = NRef second.token.span y
      p = "$record.motive"
      value = "$record.value"
      next = "$record.branch"
      self = "$record.self"
      pRef = NRef eliminatorName.span p
      valueRef = NRef eliminatorName.span value
      nextRef = NRef eliminatorName.span next
      bind = \q, binder, ty, body => NPi region q binder ty body
      lam = \q, binder, ty, body => NLambda region q binder ty body
      app = \f, arg => NApply region f arg
      fields = \body => bind first.quantity x first.ty (bind second.quantity y second.ty body)
      sigma = NSigma region first.quantity second.quantity x first.ty second.ty
      ctorType = fields typeRef
      ctorValue = lam first.quantity x first.ty (lam second.quantity y second.ty (NPairValue region typeRef xRef yRef))
      motiveType = bind Erased self typeRef (NSort eliminatorName.span level)
      branchType = fields (app pRef (app (app ctorRef xRef) yRef))
      elimType = bind Erased p motiveType (bind Linear value typeRef (bind Linear next branchType (app pRef valueRef)))
      elimValue = lam Erased p motiveType (lam Linear value typeRef (lam Linear next branchType (NPairCase region pRef valueRef nextRef)))
   in [ Declared True region name.span name.span False Erased name.spelling (NSort name.span level) sigma,
        Declared True (Between constructorKeyword.span.start constructorName.span.finish)
          constructorName.span constructorName.span False Unrestricted constructorName.spelling ctorType ctorValue,
        Declared True (Between eliminatorKeyword.span.start eliminatorName.span.finish)
          eliminatorName.span eliminatorName.span False Unrestricted eliminatorName.spelling elimType elimValue ]

parseRecord : Nat -> Position -> List Token -> Either ParseError (List Declaration, List Token)
parseRecord budget end tokens = do
  (keyword, rest) <- expect RecordKeyword end tokens
  (name, rest) <- expect Name end rest
  (_, rest) <- expect Colon end rest
  (_, rest) <- expect TypeKeyword end rest
  (universe, rest) <- expect Number end rest
  level <- levelValue universe
  (whereToken, rest) <- expect WhereKeyword end rest
  if keyword.span.start.column /= 1 || name.spelling == "_" ||
     whereToken.span.start.line /= keyword.span.start.line
     then Left (ParseFailure keyword.span.start "Expected column-one record Name : Type n where")
     else Right ()
  let indent = case rest of token :: _ => token.span.start.column; [] => 0
  (constructorKeyword, constructorName, rest) <- directive ConstructorKeyword indent end rest
  if constructorKeyword.span.start.line <= whereToken.span.start.line
     then Left (ParseFailure constructorKeyword.span.start "constructor must follow the record header")
     else Right ()
  (eliminatorKeyword, eliminatorName, rest) <- directive EliminatorKeyword indent end rest
  (first, rest) <- parseField budget indent end rest
  (second, rest) <- parseField budget indent end rest
  if first.token.spelling == second.token.spelling
     then Left (ParseFailure second.token.span.start "Duplicate record field")
     else Right ()
  case rest of
    token :: _ => if token.span.start.column > 1
                    then Left (ParseFailure token.span.start "Prototype records require exactly two single-line fields")
                    else Right ()
    [] => Right ()
  let region = Between keyword.span.start (extent second.ty).finish
  Right (recordDeclarations region name level constructorKeyword constructorName eliminatorKeyword eliminatorName first second, rest)

parseOne : Nat -> Position -> List Token -> Either ParseError (List Declaration, List Token)
parseOne budget end tokens@(token :: rest) =
  if token.kind == ExportKeyword then do
    if token.span.start.column /= 1
       then Left (ParseFailure token.span.start "export must start in column 1")
       else Right ()
    case rest of
      next :: _ => if next.kind == ExportKeyword then Left (ParseFailure next.span.start "Duplicate export marker") else Right ()
      [] => Right ()
    (decls, remaining) <- parseOne budget end rest
    case decls of
      [] => Left (ParseFailure token.span.start "Expected declaration after export")
      decl :: _ => do
        if decl.exported then Left (ParseFailure token.span.start "Duplicate export marker") else Right ()
        if decl.span.start.line <= token.span.start.line
           then Left (ParseFailure decl.span.start "export must precede the declaration on its own line")
           else Right ()
        Right (map (\item => { exported := True,
                              span := if not item.generated || item.quantity == Erased
                                         then Between token.span.start item.span.finish else item.span } item) decls, remaining)
  else if token.kind == RecordKeyword then parseRecord budget end tokens
  else do
    (decl, remaining) <- parsePair budget end tokens
    Right ([decl], remaining)
parseOne budget end [] = Left (ParseFailure end "Expected declaration")

admit : Nat -> List String -> List Declaration -> Either ParseError (Nat, List String)
admit slots seen [] = Right (slots, seen)
admit Z seen (decl :: _) = Left (ParseFailure decl.span.start "Declaration count budget exhausted")
admit (S slots) seen (decl :: rest) =
  if elem decl.name seen then Left (ParseFailure decl.nameSpan.start ("Duplicate declaration " ++ show decl.name))
     else admit slots (decl.name :: seen) rest

parseAll : Nat -> Nat -> Nat -> Position -> List String -> List Token ->
           Either ParseError (List Declaration)
parseAll fuel slots expressionBudget end seen [] = Right []
parseAll Z slots expressionBudget end seen tokens =
  Left (ParseFailure (nextPosition end tokens) "Declaration count budget exhausted")
parseAll (S fuel) slots expressionBudget end seen tokens = do
  (decls, remaining) <- parseOne expressionBudget end tokens
  (slots, seen) <- admit slots seen decls
  rest <- parseAll fuel slots expressionBudget end seen remaining
  Right (decls ++ rest)

||| Parse explicit signatures and matching definitions in source order.
||| Counts and expression recursion have independent budgets; no main check here.
public export
parseDeclarations : Nat -> Nat -> Position -> List Token ->
                    Either ParseError (List Declaration)
parseDeclarations budget expressionBudget end = parseAll budget budget expressionBudget end []

-- Synthetic entry reference is at EOF; all lowered let extents stay ordered.
-- Presence of main is checked before lowering; no source location is invented
-- for a core typing error or for a nonexistent entry.
public export
lowerDeclarations : Position -> List Declaration -> Expr
lowerDeclarations end [] = NRef (Between end end) "main"
lowerDeclarations end (decl :: rest) =
  NLet (Between decl.span.start end) decl.quantity decl.name decl.expected decl.value
       (lowerDeclarations end rest)

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
    if any exported declarations
       then Left (ParseFailure end "export requires a named module; use parseDocument")
       else Right ()
    if any (\decl => decl.name == "main") declarations
       then Right (lowerDeclarations end declarations)
       else Left (ParseFailure end "Declaration file requires a main definition")
  else parseExpression expressionBudget end tokens
