-- Fuel-bounded recursive descent for expressions, not declaration/layout syntax.
module Fibril.Source.Parser

import Data.List
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax

%default total

||| Syntax failure at a scalar position, or explicit recursion-limit exhaustion.
public export
record ParseError where
  constructor ParseFailure
  position : Position
  message : String

public export
Show ParseError where
  show err = show err.position ++ ": " ++ err.message

atInput : Position -> List Token -> Position
atInput end [] = end
atInput end (token :: _) = token.span.start

expect : TokenKind -> Position -> List Token -> Either ParseError (Token, List Token)
expect kind end [] = Left (ParseFailure end ("Expected " ++ show kind ++ ", found end of input"))
expect kind end (token :: rest) =
  if token.kind == kind then Right (token, rest)
     else Left (ParseFailure token.span.start ("Expected " ++ show kind ++ ", found " ++ show token.kind))

-- A binder-looking group is a Pi only when its matching close is followed by
-- an arrow. Otherwise (name : type) is an ordinary expression ascription.
groupArrow : Nat -> List Token -> Bool
groupArrow depth [] = False
groupArrow depth (token :: rest) =
  case token.kind of
    OpenParen => groupArrow (S depth) rest
    CloseParen =>
      case depth of
        Z => False
        S Z => case rest of
          next :: _ => next.kind == Arrow
          [] => False
        S remaining => groupArrow remaining rest
    _ => groupArrow depth rest

binderAhead : List Token -> Bool
binderAhead (Located OpenParen _ _ :: rest@(Located Name _ _ :: Located Colon _ _ :: _)) =
  groupArrow 1 rest
binderAhead (Located OpenParen _ _ :: rest@(Located Number _ _ :: Located Name _ _ :: Located Colon _ _ :: _)) =
  groupArrow 1 rest
binderAhead _ = False

startsAtom : TokenKind -> Bool
startsAtom Name = True
startsAtom TypeKeyword = True
startsAtom UnitKeyword = True
startsAtom BoolKeyword = True
startsAtom TrueKeyword = True
startsAtom FalseKeyword = True
startsAtom OpenParen = True
startsAtom _ = False

digitValue : Char -> Nat
digitValue c = cast (ord c - ord '0')

levelValue : Token -> Either ParseError Nat
levelValue token =
  let chars = unpack token.spelling
   in if length chars <= 6 && not (null chars) && all (\c => c >= '0' && c <= '9') chars
         then Right (foldl (\n, c => n * 10 + digitValue c) 0 chars)
         else Left (ParseFailure token.span.start "Universe level requires 1..6 decimal digits")

limit : Position -> List Token -> Either ParseError a
limit end tokens = Left (ParseFailure (atInput end tokens) "Parser recursion budget exhausted")

binderQuantity : List Token -> Either ParseError (Quantity, List Token)
binderQuantity [] = Right (Unrestricted, [])
binderQuantity tokens@(token :: rest) =
  if token.kind == Number
     then case token.spelling of
       "0" => Right (Erased, rest)
       "1" => Right (Linear, rest)
       _ => Left (ParseFailure token.span.start "Binder quantity must be 0 or 1 (omit for unrestricted)")
     else Right (Unrestricted, tokens)

record ParsedBinder where
  constructor Binder
  span : SourceSpan
  quantity : Quantity
  name : String
  domain : Expr
  remaining : List Token

mutual
  expression : Nat -> Position -> List Token -> Either ParseError (Expr, List Token)
  expression Z end tokens = limit end tokens
  expression (S depth) end tokens =
    case tokens of
      token :: rest =>
        if token.kind == IfKeyword then do
          (condition, afterCondition) <- expression depth end rest
          (_, afterThen) <- expect ThenKeyword end afterCondition
          (yes, afterYes) <- expression depth end afterThen
          (_, afterElse) <- expect ElseKeyword end afterYes
          (no, remaining) <- expression depth end afterElse
          Right (NIf (Between token.span.start (extent no).finish) condition yes no, remaining)
        else if token.kind == CaseKeyword then do
          (scrutinee, afterScrutinee) <- expression depth end rest
          (_, afterOf) <- expect OfKeyword end afterScrutinee
          (_, afterOpen) <- expect OpenParen end afterOf
          (_, afterClose) <- expect CloseParen end afterOpen
          (_, afterArrow) <- expect BodyArrow end afterClose
          (body, remaining) <- expression depth end afterArrow
          Right (NUnitCase (Between token.span.start (extent body).finish) scrutinee body, remaining)
        else if token.kind == LetKeyword then do
          header <- binder depth end rest
          (_, afterEquals) <- expect Equals end header.remaining
          (value, afterValue) <- expression depth end afterEquals
          (_, afterIn) <- expect InKeyword end afterValue
          (body, remaining) <- expression depth end afterIn
          Right (NLet (Between token.span.start (extent body).finish)
                      header.quantity header.name header.domain value body, remaining)
        else if token.kind == Lambda then do
          header <- binder depth end rest
          (_, afterArrow) <- expect BodyArrow end header.remaining
          (body, remaining) <- expression depth end afterArrow
          Right (NLambda (Between token.span.start (extent body).finish)
                         header.quantity header.name header.domain body, remaining)
        else if binderAhead tokens then do
          header <- binder depth end tokens
          (_, afterArrow) <- expect Arrow end header.remaining
          (body, remaining) <- expression depth end afterArrow
          Right (NPi (Between header.span.start (extent body).finish)
                     header.quantity header.name header.domain body, remaining)
        else do
          (domain, afterDomain) <- application depth end tokens
          case afterDomain of
            arrow :: rest =>
              if arrow.kind == Arrow then do
                (body, remaining) <- expression depth end rest
                Right (NPi (Between (extent domain).start (extent body).finish)
                           Unrestricted "_" domain body, remaining)
              else Right (domain, afterDomain)
            [] => Right (domain, [])
      [] => Left (ParseFailure end "Expected expression")

  -- A binder domain is parsed before adding the name to any scope.
  binder : Nat -> Position -> List Token -> Either ParseError ParsedBinder
  binder Z end tokens = limit end tokens
  binder (S depth) end tokens = do
    (opening, rest) <- expect OpenParen end tokens
    (q, afterQuantity) <- binderQuantity rest
    (name, afterName) <- expect Name end afterQuantity
    (_, afterColon) <- expect Colon end afterName
    (domain, afterDomain) <- expression depth end afterColon
    (closing, remaining) <- expect CloseParen end afterDomain
    Right (Binder (Between opening.span.start closing.span.finish) q name.spelling domain remaining)

  application : Nat -> Position -> List Token -> Either ParseError (Expr, List Token)
  application Z end tokens = limit end tokens
  application (S depth) end tokens = do
    (head, remaining) <- atom depth end tokens
    arguments depth end head remaining

  arguments : Nat -> Position -> Expr -> List Token -> Either ParseError (Expr, List Token)
  arguments depth end function [] = Right (function, [])
  arguments Z end function tokens = limit end tokens
  arguments (S depth) end function tokens@(token :: rest) =
    if startsAtom token.kind then do
      (argument, remaining) <- atom depth end tokens
      arguments depth end
        (NApply (Between (extent function).start (extent argument).finish) function argument) remaining
    else Right (function, tokens)

  atom : Nat -> Position -> List Token -> Either ParseError (Expr, List Token)
  atom Z end tokens = limit end tokens
  atom (S depth) end [] = Left (ParseFailure end "Expected expression atom")
  atom (S depth) end (token :: rest) =
    case token.kind of
      Name => Right (NRef token.span token.spelling, rest)
      UnitKeyword => Right (NUnitType token.span, rest)
      BoolKeyword => Right (NBoolType token.span, rest)
      TrueKeyword => Right (NBoolValue token.span True, rest)
      FalseKeyword => Right (NBoolValue token.span False, rest)
      TypeKeyword => do
        (level, remaining) <- expect Number end rest
        value <- levelValue level
        Right (NSort (Between token.span.start level.span.finish) value, remaining)
      OpenParen => grouped depth end token rest
      _ => Left (ParseFailure token.span.start "Expected name, Type LEVEL, Unit, (), Bool, True, False, or grouped expression")

  grouped : Nat -> Position -> Token -> List Token -> Either ParseError (Expr, List Token)
  grouped depth end opening (closing :: remaining) =
    if closing.kind == CloseParen
       then Right (NUnitValue (Between opening.span.start closing.span.finish), remaining)
       else groupExpression depth end opening (closing :: remaining)
  grouped depth end opening [] = Left (ParseFailure end "Expected expression or )")

  groupExpression : Nat -> Position -> Token -> List Token -> Either ParseError (Expr, List Token)
  groupExpression depth end token rest = do
    (inner, afterInner) <- expression depth end rest
    case afterInner of
      colon :: afterColon =>
        if colon.kind == Colon then do
          (expected, afterType) <- expression depth end afterColon
          (closing, remaining) <- expect CloseParen end afterType
          Right (NAscribe (Between token.span.start closing.span.finish) inner expected, remaining)
        else do
          (closing, remaining) <- expect CloseParen end afterInner
          Right (withExtent (Between token.span.start closing.span.finish) inner, remaining)
      [] => Left (ParseFailure end "Expected )")

||| Parse one complete token stream; trailing tokens are errors.
||| Budget limits recursive depth/argument chains, not elapsed time or memory.
||| The supplied end position should be the end of the original decoded source.
public export
parseExpression : Nat -> Position -> List Token -> Either ParseError Expr
parseExpression budget end tokens = do
  (term, remaining) <- expression budget end tokens
  case remaining of
    [] => Right term
    token :: _ => Left (ParseFailure token.span.start "Unexpected trailing token")
