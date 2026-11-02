-- Fuel-bounded recursive descent for expressions, not declaration/layout syntax.
module Fibril.Source.Parser

import Data.List
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.StringLiteral

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

||| Consume one required token; shared by expression and declaration framing.
public export
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
startsAtom StringToken = True
startsAtom StringKeyword = True
startsAtom UnitKeyword = True
startsAtom BoolKeyword = True
startsAtom TrueKeyword = True
startsAtom FalseKeyword = True
startsAtom OpenParen = True
startsAtom _ = False

digitValue : Char -> Nat
digitValue c = cast (ord c - ord '0')

public export
levelValue : Token -> Either ParseError Nat
levelValue token =
  let chars = unpack token.spelling
   in if length chars <= 6 && not (null chars) && all (\c => c >= '0' && c <= '9') chars
         then Right (foldl (\n, c => n * 10 + digitValue c) 0 chars)
         else Left (ParseFailure token.span.start "Universe level requires 1..6 decimal digits")

limit : Position -> List Token -> Either ParseError a
limit end tokens = Left (ParseFailure (atInput end tokens) "Parser recursion budget exhausted")

||| Read an optional 0/1 prefix; omitted means unrestricted.
public export
binderQuantity : List Token -> Either ParseError (Quantity, List Token)
binderQuantity [] = Right (Unrestricted, [])
binderQuantity tokens@(token :: rest) =
  if token.kind == Number
     then case token.spelling of
       "0" => Right (Erased, rest)
       "1" => Right (Linear, rest)
       _ => Left (ParseFailure token.span.start "Binder quantity must be 0 or 1 (omit for unrestricted)")
     else Right (Unrestricted, tokens)

public export
record ParsedBinder where
  constructor Binder
  span : SourceSpan
  quantity : Quantity
  name : String
  domain : Expr
  remaining : List Token

||| Decode a validated string token, shared by core and console parsing.
public export
literalValue : Token -> Either ParseError String
literalValue token = do
  if token.kind /= StringToken
     then Left (ParseFailure token.span.start "Expected string token")
     else Right ()
  decoded <- case scanLiteral token.span.start (unpack token.spelling) of
    Left err => Left (ParseFailure err.position err.message)
    Right decoded => Right decoded
  case decoded.remaining of
    [] => Right decoded.value
    _ => Left (ParseFailure token.span.start "Malformed string token")

qualifiedAhead : List Token -> Bool
qualifiedAhead (dot :: _) = dot.kind == Dot
qualifiedAhead _ = False

-- Prefix components occupy the module namespace; the final value name is an
-- ordinary identifier. Dots are not general value/member projection.
qualifiedReference : Nat -> Position -> Token -> Token -> List String -> List Token ->
            Either ParseError (Expr, List Token)
qualifiedReference Z end first current segments rest =
  Left (ParseFailure current.span.start "Qualified name component budget exhausted")
qualifiedReference (S budget) end first current segments rest =
  case rest of
    dot :: next :: remaining =>
      if dot.kind == Dot then
        if not (validModuleComponent current.spelling)
           then Left (ParseFailure current.span.start "Expected uppercase module qualifier")
        else if dot.span.start.line /= first.span.start.line ||
                next.span.start.line /= first.span.start.line
           then Left (ParseFailure dot.span.start "Qualified names must occupy one source line")
        else qualifiedReference budget end first next (current.spelling :: segments) remaining
      else finish
    [dot] => if dot.kind == Dot then Left (ParseFailure end "Expected qualified value name") else finish
    [] => finish
  where
    finish : Either ParseError (Expr, List Token)
    finish =
      if current.kind == Name && current.spelling /= "_" && not (null segments)
         then Right (NQualifiedRef (Between first.span.start current.span.finish)
                         (concat (intersperse "." (reverse (current.spelling :: segments)))), rest)
         else Left (ParseFailure current.span.start "Expected qualified value identifier")

data DoStatement = Action Expr | Binding SourceSpan String Expr Expr
                 | LocalBinding SourceSpan Quantity String Expr Expr

statementExtent : DoStatement -> SourceSpan
statementExtent (Action action) = extent action
statementExtent (Binding span _ _ _) = span
statementExtent (LocalBinding span _ _ _ _) = span

sequenceExpressions : Position -> DoStatement -> List DoStatement -> Either ParseError Expr
sequenceExpressions start (Action first) [] =
  Right (withExtent (Between start (extent first).finish) first)
sequenceExpressions start (Binding span _ _ _) [] =
  Left (ParseFailure span.start "do binding requires a following action")
sequenceExpressions start (LocalBinding span _ _ _ _) [] =
  Left (ParseFailure span.start "do let requires a following action")
sequenceExpressions start first (next :: rest) = do
  body <- sequenceExpressions (statementExtent next).start next rest
  let span = Between start (extent body).finish
  case first of
    Action action => Right (NSequence span action body)
    Binding _ name domain action => Right (NDoBind span name domain action body)
    LocalBinding _ q name domain value => Right (NLet span q name domain value body)

mutual
  expression : Nat -> Position -> List Token -> Either ParseError (Expr, List Token)
  expression Z end tokens = limit end tokens
  expression (S depth) end tokens =
    case tokens of
      token :: rest =>
        if token.kind == DoKeyword then do
          (resultType, statements) <- the (Either ParseError (Maybe Expr, List Token)) $ case rest of
            opening :: _ =>
              if opening.kind == OpenParen && opening.span.start.line == token.span.start.line
                 then do
                   (ty, remaining) <- atom depth end rest
                   Right (Just ty, remaining)
                 else Right (Nothing, rest)
            [] => Right (Nothing, [])
          let headerLine : Nat = case resultType of
                Nothing => token.span.start.line
                Just ty => (extent ty).finish.line
          case statements of
            [] => Left (ParseFailure end "do block requires at least one action")
            first :: _ =>
              if first.span.start.line <= headerLine || first.span.start.column <= 1
                 then Left (ParseFailure first.span.start "do actions require indented following lines")
                 else do
                   (actions, remaining) <- doActions depth 64 end first.span.start.column
                                                      headerLine statements
                   case actions of
                     [] => Left (ParseFailure end "do block requires at least one action")
                     first :: rest => do
                       body <- sequenceExpressions token.span.start first rest
                       Right (case resultType of
                         Nothing => body
                         Just ty => NDoResult (Between token.span.start (extent body).finish) ty body,
                         remaining)
        else if token.kind == IfKeyword then do
          (condition, afterCondition) <- expression depth end rest
          (_, afterThen) <- expect ThenKeyword end afterCondition
          (yes, afterYes) <- expression depth end afterThen
          (_, afterElse) <- expect ElseKeyword end afterYes
          (no, remaining) <- expression depth end afterElse
          Right (NIf (Between token.span.start (extent no).finish) condition yes no, remaining)
        else if token.kind == CaseKeyword then do
          (scrutinee, afterScrutinee) <- expression depth end rest
          case afterScrutinee of
            marker :: afterReturn =>
              if marker.kind == ReturnKeyword then pairCase depth end token scrutinee afterReturn
                 else unitCase depth end token scrutinee afterScrutinee
            [] => unitCase depth end token scrutinee afterScrutinee
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

  pairCase : Nat -> Position -> Token -> Expr -> List Token -> Either ParseError (Expr, List Token)
  pairCase depth end token scrutinee afterReturn = do
    (motive, afterMotive) <- expression depth end afterReturn
    (_, afterOf) <- expect OfKeyword end afterMotive
    first <- binder depth end afterOf
    second <- binder depth end first.remaining
    if first.name == second.name && first.name /= "_"
       then Left (ParseFailure second.span.start "Record pattern binders must be distinct")
       else Right ()
    (_, afterArrow) <- expect BodyArrow end second.remaining
    (body, remaining) <- expression depth end afterArrow
    let branch = NLambda (Between first.span.start (extent body).finish)
                   first.quantity first.name first.domain
                   (NLambda (Between second.span.start (extent body).finish)
                     second.quantity second.name second.domain body)
    Right (NPairCase (Between token.span.start (extent body).finish) motive scrutinee branch, remaining)

  unitCase : Nat -> Position -> Token -> Expr -> List Token -> Either ParseError (Expr, List Token)
  unitCase depth end token scrutinee tokens = do
    (_, afterOf) <- expect OfKeyword end tokens
    (_, afterOpen) <- expect OpenParen end afterOf
    (_, afterClose) <- expect CloseParen end afterOpen
    (_, afterArrow) <- expect BodyArrow end afterClose
    (body, remaining) <- expression depth end afterArrow
    Right (NUnitCase (Between token.span.start (extent body).finish) scrutinee body, remaining)

  doStatement : Nat -> Position -> List Token -> Either ParseError (DoStatement, List Token)
  doStatement depth end tokens@(opening :: _) =
    if opening.kind == LetKeyword then do
      header <- binder depth end (drop 1 tokens)
      (_, afterEquals) <- expect Equals end header.remaining
      (value, rest) <- expression depth end afterEquals
      case rest of
        token :: _ =>
          if token.kind == InKeyword then do
            -- Preserve existing complete let ... in ... action expressions.
            (action, rest) <- expression depth end tokens
            Right (Action action, rest)
          else Right (LocalBinding (Between opening.span.start (extent value).finish)
                        header.quantity header.name header.domain value, rest)
        [] => Right (LocalBinding (Between opening.span.start (extent value).finish)
                      header.quantity header.name header.domain value, [])
    else if opening.kind == OpenParen && any (\token => token.kind == BindArrow) tokens
       then do
         header <- binder depth end tokens
         if header.quantity /= Linear
            then Left (ParseFailure header.span.start "do result bindings require explicit quantity 1")
            else Right ()
         (_, afterArrow) <- expect BindArrow end header.remaining
         (action, rest) <- expression depth end afterArrow
         Right (Binding (Between header.span.start (extent action).finish)
                        header.name header.domain action, rest)
       else do
         (action, rest) <- expression depth end tokens
         Right (Action action, rest)
  doStatement depth end [] = Left (ParseFailure end "Expected do statement")

  doActions : Nat -> Nat -> Position -> Nat -> Nat -> List Token ->
              Either ParseError (List DoStatement, List Token)
  doActions depth budget end column previous [] = Right ([], [])
  doActions depth Z end column previous tokens@(token :: _) =
    if token.span.start.column < column then Right ([], tokens)
       else Left (ParseFailure token.span.start "do action count budget exhausted")
  doActions depth (S budget) end column previous tokens@(token :: _) =
    if token.span.start.column < column then Right ([], tokens)
    else if token.span.start.column /= column || token.span.start.line <= previous
       then Left (ParseFailure token.span.start "do actions must occupy separate equally indented lines")
       else do
         let (chunk, remaining) = Data.List.span
               (\item => item.span.start.line == token.span.start.line) tokens
         (action, trailing) <- doStatement depth (atInput end remaining) chunk
         case trailing of
           extra :: _ => Left (ParseFailure extra.span.start "Unexpected tokens after do action")
           [] => do
             (actions, rest) <- doActions depth budget end column (statementExtent action).finish.line remaining
             Right (action :: actions, rest)

  -- A binder domain is parsed before adding the name to any scope.
  public export
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
    if qualifiedAhead rest then qualifiedReference 17 end token token [] rest else
    case token.kind of
      Name => Right (NRef token.span token.spelling, rest)
      StringToken => do
        value <- literalValue token
        Right (NStringValue token.span value, rest)
      StringKeyword => Right (NStringType token.span, rest)
      UnitKeyword => Right (NUnitType token.span, rest)
      BoolKeyword => Right (NBoolType token.span, rest)
      TrueKeyword => Right (NBoolValue token.span True, rest)
      FalseKeyword => Right (NBoolValue token.span False, rest)
      TypeKeyword => do
        (level, remaining) <- expect Number end rest
        value <- levelValue level
        Right (NSort (Between token.span.start level.span.finish) value, remaining)
      OpenParen => grouped depth end token rest
      _ => Left (ParseFailure token.span.start "Expected name, Type LEVEL, String/literal, Unit, (), Bool, True, False, or grouped expression")

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
