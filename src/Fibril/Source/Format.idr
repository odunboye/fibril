-- Conservative whitespace formatting. Preserve all trivia outside horizontal gaps.
module Fibril.Source.Format

import Data.List
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Document
import Fibril.Source.Shape
import Fibril.Source.Syntax
import Fibril.Source.Declaration.Syntax

%default total

public export
data FormatError = FormatDocument DocumentError | FormatShapeChanged | FormatSizeLimit

byteCount : String -> Nat
byteCount source = foldl (\count, char => count +
  (if ord char <= 0x7f then 1 else if ord char <= 0x7ff then 2 else if ord char <= 0xffff then 3 else 4)) 0 (unpack source)

horizontal : Char -> Bool
horizontal char = char == ' ' || char == '\t'

separator : Token -> Token -> List Char
separator previous next =
  if previous.kind == Dot || next.kind == Dot || next.kind == Comma ||
     previous.kind == OpenParen || next.kind == CloseParen ||
     previous.kind == DictionaryOpen || previous.kind == OpenBrace || next.kind == CloseBrace ||
     (previous.kind == Lambda && next.kind == OpenParen) ||
     -- `5w` is one Word literal: the suffix must stay attached to its digits.
     (previous.kind == Number && next.kind == Name && next.spelling == "w" &&
      previous.span.finish.offset == next.span.start.offset)
     then [] else [' ']

quoteState : TokenKind -> (Bool, List Bool) -> (Bool, List Bool)
quoteState kind (quoted, frames) =
  if kind == Backtick then (not quoted, frames)
  else if kind == OpenParen || kind == OpenBrace || kind == DictionaryOpen then (False, quoted :: frames)
  else if kind == CloseParen || kind == CloseBrace then case frames of
    [] => (False, [])
    outer :: rest => (outer, rest)
  else (quoted, frames)

formatTokens : Maybe Token -> (Bool, List Bool) -> Nat -> List Char -> List Token -> List Char
formatTokens previous state offset chars [] = chars
formatTokens previous state@(quoted, frames) offset chars (token :: rest) =
  let (gap, following) = splitAt (minus token.span.start.offset offset) chars
      (original, remaining) = splitAt (minus token.span.finish.offset token.span.start.offset) following
      spacing = case previous of
        Just before => if before.span.finish.line == token.span.start.line && all horizontal gap
                          then if quoted && (token.kind == Backtick || before.kind == Backtick)
                                  then [] else separator before token
                          else gap
        Nothing => gap
   in spacing ++ original ++ formatTokens (Just token) (quoteState token.kind state) token.span.finish.offset remaining rest

-- Layout decisions depend on flattened token width, not current line breaks.
-- That makes already-multiline definitions and repeat formatting consistent.
Plan : Type
Plan = List (Nat, Nat)

inside : SourceSpan -> Token -> Bool
inside region token = token.span.start.offset >= region.start.offset &&
                      token.span.finish.offset <= region.finish.offset

flatWidth : List Token -> SourceSpan -> Nat
flatWidth tokens region = measure Nothing (filter (inside region) tokens)
  where
    measure : Maybe Token -> List Token -> Nat
    measure previous [] = 0
    measure previous (token :: rest) =
      let gap = case previous of Nothing => 0; Just before => length (separator before token)
       in gap + minus token.span.finish.offset token.span.start.offset + measure (Just token) rest

wide : List Token -> Nat -> Expr -> Bool
wide tokens indentation value = indentation + flatWidth tokens (extent value) > 92

atStart : Nat -> Expr -> Plan
atStart indentation value = [((extent value).start.offset, indentation)]

keyword : List Token -> TokenKind -> Nat -> Nat -> Nat -> Plan
keyword tokens kind begin end indentation =
  case find (\token => token.kind == kind && token.span.start.offset >= begin &&
                       token.span.finish.offset <= end) tokens of
    Just token => [(token.span.start.offset, indentation)]
    Nothing => []

hasArrow : List Token -> TokenKind -> Expr -> Expr -> Bool
hasArrow tokens kind domain body =
  not (null (keyword tokens kind (extent domain).finish.offset (extent body).start.offset 0))

grouped : List Token -> Expr -> Bool
grouped tokens value = any (\token => token.kind == OpenParen &&
                           token.span.start.offset == (extent value).start.offset) tokens

layout : List Token -> Nat -> Bool -> Expr -> Plan
layout tokens indentation forced (NImplementationApply _ _ function) = layout tokens indentation forced function
layout tokens indentation forced (NDictionaryApply _ _ function Nothing) = layout tokens indentation forced function
layout tokens indentation forced (NDictionaryApply _ _ function (Just value)) =
  layout tokens indentation forced function ++ layout tokens (indentation + 2) False value
layout tokens indentation forced value@(NInfix _ function left right) =
  layout tokens indentation False left ++ layout tokens (indentation + 2) False function ++
  layout tokens (indentation + 2) False right ++
  (if forced || wide tokens indentation value
      then keyword tokens Backtick (extent left).finish.offset (extent function).start.offset (indentation + 2)
      else [])
layout tokens indentation forced (NImplicitApply _ function argument) =
  layout tokens indentation forced function ++ layout tokens (indentation + 2) False argument
layout tokens indentation forced value@(NApply _ function argument) =
  let split = forced || wide tokens indentation value
      groupedArgument = grouped tokens argument
      breaking = split && (groupedArgument || (wide tokens (indentation + 2) value && not (wide tokens (indentation + 2) argument)))
      childIndent = if breaking then indentation + 2 else indentation
   in (if breaking then atStart (indentation + 2) argument else []) ++
      layout tokens indentation split function ++ layout tokens childIndent (split && groupedArgument) argument
layout tokens indentation forced value@(NLambda _ _ _ domain body) =
  let split = (forced || wide tokens indentation value) && hasArrow tokens BodyArrow domain body
      childIndent = if split then indentation + 2 else indentation
   in (if split then atStart childIndent body else []) ++
      layout tokens (indentation + 2) False domain ++
      layout tokens childIndent (forced && not (hasArrow tokens BodyArrow domain body)) body
layout tokens indentation forced value@(NImplicitPi _ _ _ domain body) =
  let split = forced || wide tokens indentation value
   in (if split && hasArrow tokens Arrow domain body then atStart (indentation + 2) body else []) ++
      layout tokens (indentation + 2) False domain ++ layout tokens indentation split body
layout tokens indentation forced value@(NConstraintPi _ _ _ domain body) =
  let split = forced || wide tokens indentation value
   in (if split && hasArrow tokens BodyArrow domain body then atStart (indentation + 2) body else []) ++
      layout tokens (indentation + 2) False domain ++ layout tokens indentation split body
layout tokens indentation forced value@(NPi _ _ _ domain body) =
  let split = forced || wide tokens indentation value
   in (if split && hasArrow tokens Arrow domain body then atStart (indentation + 2) body else []) ++
      layout tokens (indentation + 2) False domain ++ layout tokens indentation split body
layout tokens indentation forced value@(NPairCase _ motive scrutinee branch) =
  let split = forced || wide tokens indentation value
   in (if split then
         keyword tokens ReturnKeyword (extent scrutinee).finish.offset (extent motive).start.offset (indentation + 2) ++
         keyword tokens OfKeyword (extent motive).finish.offset (extent branch).start.offset (indentation + 2)
       else []) ++
      layout tokens indentation split scrutinee ++
      layout tokens (indentation + 4) False motive ++
      layout tokens (indentation + 2) split branch
layout tokens indentation forced value@(NBoxCase _ motive scrutinee branch) =
  let split = forced || wide tokens indentation value
   in (if split then
         keyword tokens ReturnKeyword (extent scrutinee).finish.offset (extent motive).start.offset (indentation + 2) ++
         keyword tokens OfKeyword (extent motive).finish.offset (extent branch).start.offset (indentation + 2)
       else []) ++
      layout tokens indentation split scrutinee ++
      layout tokens (indentation + 4) False motive ++
      layout tokens (indentation + 2) split branch
layout tokens indentation forced (NEquationLambda _ _ _ body) = layout tokens indentation forced body
layout tokens indentation forced value@(NPatternLambda _ _ body) =
  let split = forced || wide tokens indentation value
   in (if split then atStart (indentation + 2) body else []) ++
      layout tokens (if split then indentation + 2 else indentation) False body
layout tokens indentation forced (NCaseEither _ asRecord _) = layout tokens indentation forced asRecord
layout tokens indentation forced value@(NConstructorCase _ _ constructor scrutinee branch motive) =
  let split = forced || wide tokens indentation value
      markers = if split then
        keyword tokens OfKeyword (extent scrutinee).finish.offset (extent constructor).start.offset (indentation + 2) ++
        (case motive of
          Nothing => []
          Just result => keyword tokens ReturnKeyword (extent scrutinee).finish.offset (extent result).start.offset (indentation + 2))
        else []
   in markers ++ layout tokens indentation split scrutinee ++
      layout tokens (indentation + 2) False constructor ++
      (case motive of Nothing => []; Just result => layout tokens (indentation + 4) False result) ++
      layout tokens (indentation + 2) split branch
layout tokens indentation forced value@(NInferCase _ _ scrutinee branch) =
  let split = forced || wide tokens indentation value
   in (if split then keyword tokens OfKeyword (extent scrutinee).finish.offset (extent branch).start.offset (indentation + 2) else []) ++
      layout tokens indentation split scrutinee ++ layout tokens (indentation + 2) split branch
layout tokens indentation forced value@(NIf _ condition yes no) =
  let split = forced || wide tokens indentation value
   in (if split then
         keyword tokens ThenKeyword (extent condition).finish.offset (extent yes).start.offset (indentation + 2) ++
         keyword tokens ElseKeyword (extent yes).finish.offset (extent no).start.offset (indentation + 2)
       else []) ++
      layout tokens indentation False condition ++
      layout tokens (indentation + 4) False yes ++ layout tokens (indentation + 4) False no
layout tokens indentation forced value@(NUnitCase _ scrutinee body) =
  let split = forced || wide tokens indentation value
   in (if split then keyword tokens OfKeyword (extent scrutinee).finish.offset (extent body).start.offset (indentation + 2) ++
                     atStart (indentation + 4) body else []) ++
      layout tokens indentation False scrutinee ++ layout tokens (indentation + 4) False body
layout tokens indentation forced value@(NLet _ _ _ domain expression body) =
  let split = forced || wide tokens indentation value
   in (if split then keyword tokens InKeyword (extent expression).finish.offset (extent body).start.offset indentation else []) ++
      layout tokens indentation False domain ++ layout tokens (indentation + 2) False expression ++
      layout tokens (indentation + 2) False body
layout tokens indentation forced (NAscribe _ value ty) =
  layout tokens indentation forced value ++ layout tokens indentation False ty
layout tokens indentation forced (NSigma _ _ _ _ a b) = layout tokens indentation False a ++ layout tokens indentation False b
layout tokens indentation forced (NPairValue _ a b c) =
  layout tokens indentation False a ++ layout tokens indentation False b ++ layout tokens indentation False c
layout _ _ _ _ = []

planExpression : List Token -> Nat -> Expr -> Plan
planExpression tokens allowance expression =
  -- Existing do statements are physically line-framed. Don't partially reflow
  -- their enclosing expression until a multiline-do grammar is available.
  let scoped = filter (inside (extent expression)) tokens
   in if any (\token => token.kind == DoKeyword) scoped
         then [] else layout scoped 0 (allowance + flatWidth scoped (extent expression) > 100) expression

breakpoints : ParsedDocument -> Plan
breakpoints document = case document.body of
  ExpressionDocument value => planExpression document.tokens 0 value
  DeclarationDocument authored => concatMap (\item => case item of
    Ordinary decl => planExpression document.tokens (length (unpack decl.name) + 5) decl.expected ++
                     planExpression document.tokens (length (unpack decl.name) + 3) decl.value
    ImplementationBlock block => concatMap (\method =>
      let indentation = minus method.name.span.start.column 1
       in map (\(point, column) => (point, column + indentation))
            (planExpression document.tokens (indentation + length (unpack method.name.spelling) + 3) method.value)) block.methods
    ImplementationItem decl => planExpression document.tokens (length (unpack decl.name) + 20) decl.expected ++
                               planExpression document.tokens (length (unpack decl.name) + 3) decl.value
    MutualItem _ => []
    DataItem _ => []
    RecordItem _ => []
    InterfaceItem _ => []) authored
  EmptyDocument => []

-- Preserve homogeneous newline styles; mixed/lone-CR input gets spacing only.
newlineStyle : Bool -> Bool -> List Char -> Maybe (List Char)
newlineStyle lf crlf [] = if crlf then Just ['\r', '\n'] else Just ['\n']
newlineStyle lf crlf ('\r' :: '\n' :: rest) =
  if lf then Nothing else newlineStyle lf True rest
newlineStyle lf crlf ('\r' :: _) = Nothing
newlineStyle lf crlf ('\n' :: rest) =
  if crlf then Nothing else newlineStyle True crlf rest
newlineStyle lf crlf (_ :: rest) = newlineStyle lf crlf rest

whitespace : Char -> Bool
whitespace char = horizontal char || char == '\n' || char == '\r'

layoutGap : List Char -> List Char -> Nat -> List Char
layoutGap newline gap indentation =
  if all horizontal gap then newline ++ replicate indentation ' '
  else reverse (dropWhile horizontal (reverse gap)) ++ replicate indentation ' '

wrapTokens : Plan -> List Char -> Nat -> List Char -> List Token -> List Char
wrapTokens points newline offset chars [] = chars
wrapTokens points newline offset chars (token :: rest) =
  let (gap, following) = splitAt (minus token.span.start.offset offset) chars
      (original, remaining) = splitAt (minus token.span.finish.offset token.span.start.offset) following
      spacing = case lookup token.span.start.offset points of
        Just indentation => if all whitespace gap then layoutGap newline gap indentation else gap
        Nothing => gap
   in spacing ++ original ++ wrapTokens points newline token.span.finish.offset remaining rest

wrapApplications : String -> ParsedDocument -> String
wrapApplications source document = case newlineStyle False False (unpack source) of
  Nothing => source
  Just newline =>
    let proposed = pack (wrapTokens (breakpoints document) newline 0 (unpack source) document.tokens)
     in if byteCount proposed > 65536 then source else case parseDocument 64 256 proposed of
          Left _ => source
          Right candidate => if sameDocumentShape document candidate then proposed else source

||| Never expands records, evaluates code, changes literals, or writes source.
||| Candidate parsing and shape comparison are runtime guards, not a proof theorem.
public export
formatSource : String -> Either FormatError String
formatSource source = do
  if byteCount source > 65536 then Left FormatSizeLimit else Right ()
  original <- case parseDocument 64 256 source of
    Left err => Left (FormatDocument err)
    Right document => Right document
  let formatted = pack (formatTokens Nothing (False, []) 0 (unpack source) original.tokens)
  if byteCount formatted > 65536 then Left FormatSizeLimit else Right ()
  candidate <- case parseDocument 64 256 formatted of
    Left _ => Left FormatShapeChanged
    Right document => Right document
  if sameDocumentShape original candidate then Right (wrapApplications formatted candidate) else Left FormatShapeChanged
