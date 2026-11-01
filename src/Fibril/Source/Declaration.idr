-- Small source-ordered declaration files, not a module/import/recursion system.
module Fibril.Source.Declaration

import Data.List
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Parser

%default total

||| A signature/definition pair before lexical resolution or type checking.
public export
record Declaration where
  constructor Defined
  span : SourceSpan
  quantity : Quantity
  name : String
  expected : Expr
  value : Expr

nextPosition : Position -> List Token -> Position
nextPosition end [] = end
nextPosition end (token :: _) = token.span.start

-- The header's remaining tokens and later indented lines form one expression.
-- A later column-one token always starts the next declaration frame.
expressionChunk : Nat -> List Token -> (List Token, List Token)
expressionChunk headerLine =
  span (\token => token.span.start.line == headerLine || token.span.start.column > 1)

parseOne : Nat -> Position -> List Token ->
           Either ParseError (Declaration, List Token)
parseOne expressionBudget end [] = Left (ParseFailure end "Expected declaration signature")
parseOne expressionBudget end tokens@(first :: _) = do
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
                 q name.spelling expected value, remaining)

parseAll : Nat -> Nat -> Position -> List String -> List Token ->
           Either ParseError (List Declaration)
parseAll budget expressionBudget end seen [] = Right []
parseAll Z expressionBudget end seen tokens =
  Left (ParseFailure (nextPosition end tokens) "Declaration count budget exhausted")
parseAll (S budget) expressionBudget end seen tokens = do
  (decl, remaining) <- parseOne expressionBudget end tokens
  if elem decl.name seen
     then Left (ParseFailure decl.span.start ("Duplicate declaration " ++ show decl.name))
     else do
       rest <- parseAll budget expressionBudget end (decl.name :: seen) remaining
       Right (decl :: rest)

||| Parse explicit signatures and matching definitions in source order.
||| Counts and expression recursion have independent budgets; no main check here.
public export
parseDeclarations : Nat -> Nat -> Position -> List Token ->
                    Either ParseError (List Declaration)
parseDeclarations budget expressionBudget end = parseAll budget expressionBudget end []

-- Synthetic entry reference is at EOF; all lowered let extents stay ordered.
-- Presence of main is checked before lowering; no source location is invented
-- for a core typing error or for a nonexistent entry.
lowerDeclarations : Position -> List Declaration -> Expr
lowerDeclarations end [] = NRef (Between end end) "main"
lowerDeclarations end (decl :: rest) =
  NLet (Between decl.span.start end) decl.quantity decl.name decl.expected decl.value
       (lowerDeclarations end rest)

declarationAhead : List Token -> Bool
declarationAhead (Located Name _ _ :: Located Colon _ _ :: _) = True
declarationAhead (Located Name _ _ :: Located Equals _ _ :: _) = True
declarationAhead (Located Number _ _ :: _) = True
declarationAhead _ = False

||| Accept an expression or a nonrecursive declaration file with fixed main entry.
||| Declarations elaborate to existing typed lets; no new trusted core rule.
public export
parseSource : (declarationBudget, expressionBudget : Nat) -> Position ->
              List Token -> Either ParseError Expr
parseSource declarationBudget expressionBudget end tokens =
  if declarationAhead tokens then do
    declarations <- parseDeclarations declarationBudget expressionBudget end tokens
    if any (\decl => decl.name == "main") declarations
       then Right (lowerDeclarations end declarations)
       else Left (ParseFailure end "Declaration file requires a main definition")
  else parseExpression expressionBudget end tokens
