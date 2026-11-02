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
  if previous.kind == Dot || next.kind == Dot ||
     previous.kind == OpenParen || next.kind == CloseParen ||
     (previous.kind == Lambda && next.kind == OpenParen)
     then [] else [' ']

formatTokens : Maybe Token -> Nat -> List Char -> List Token -> List Char
formatTokens previous offset chars [] = chars
formatTokens previous offset chars (token :: rest) =
  let (gap, following) = splitAt (minus token.span.start.offset offset) chars
      (original, remaining) = splitAt (minus token.span.finish.offset token.span.start.offset) following
      spacing = case previous of
        Just before => if before.span.finish.line == token.span.start.line && all horizontal gap
                          then separator before token else gap
        Nothing => gap
   in spacing ++ original ++ formatTokens (Just token) token.span.finish.offset remaining rest

-- Grouped application arguments are safe candidate breakpoints, not arbitrary
-- parentheses (which may be binder/header syntax).
arguments : Expr -> List Nat
arguments (NApply _ function argument) =
  (extent argument).start.offset :: (arguments function ++ arguments argument)
arguments (NIf _ c t e) = arguments c ++ arguments t ++ arguments e
arguments (NUnitCase _ a b) = arguments a ++ arguments b
arguments (NPi _ _ _ a b) = arguments a ++ arguments b
arguments (NLambda _ _ _ a b) = arguments a ++ arguments b
arguments (NSigma _ _ _ _ a b) = arguments a ++ arguments b
arguments (NPairValue _ a b c) = arguments a ++ arguments b ++ arguments c
arguments (NPairCase _ a b c) = arguments a ++ arguments b ++ arguments c
arguments (NAscribe _ a b) = arguments a ++ arguments b
arguments (NLet _ _ _ a b c) = arguments a ++ arguments b ++ arguments c
-- Do layout is physical-line based; don't wrap within its desugared statements.
arguments (NSequence _ _ _) = []
arguments (NDoBind _ _ _ _ _) = []
arguments (NDoResult _ _ _) = []
arguments _ = []

longExpression : Expr -> List Nat
longExpression value =
  if (extent value).start.line == (extent value).finish.line &&
     minus (extent value).finish.column 1 > 100 then arguments value else []

breakpoints : ParsedDocument -> List Nat
breakpoints document =
  let proposed = case document.body of
        ExpressionDocument value => longExpression value
        DeclarationDocument authored => concatMap (\item => case item of
          Ordinary decl => longExpression decl.value
          RecordItem _ => []) authored
        EmptyDocument => []
   in map (\token => token.span.start.offset)
        (filter (\token => token.kind == OpenParen && elem token.span.start.offset proposed) document.tokens)

-- Preserve homogeneous newline styles; mixed/lone-CR input gets spacing only.
newlineStyle : Bool -> Bool -> List Char -> Maybe (List Char)
newlineStyle lf crlf [] = if crlf then Just ['\r', '\n'] else Just ['\n']
newlineStyle lf crlf ('\r' :: '\n' :: rest) =
  if lf then Nothing else newlineStyle lf True rest
newlineStyle lf crlf ('\r' :: _) = Nothing
newlineStyle lf crlf ('\n' :: rest) =
  if crlf then Nothing else newlineStyle True crlf rest
newlineStyle lf crlf (_ :: rest) = newlineStyle lf crlf rest

wrapTokens : List Nat -> List Char -> Nat -> Nat -> Maybe Token -> Nat ->
             List Char -> List Token -> List Char
wrapTokens points newline nesting indentation previous offset chars [] = chars
wrapTokens points newline nesting indentation previous offset chars (token :: rest) =
  let (gap, following) = splitAt (minus token.span.start.offset offset) chars
      (original, remaining) = splitAt (minus token.span.finish.offset token.span.start.offset) following
      base = case previous of
        Just before => if before.span.finish.line /= token.span.start.line
                          then minus token.span.start.column 1 else indentation
        Nothing => minus token.span.start.column 1
      spacing = if elem token.span.start.offset points && all horizontal gap
                   then newline ++ replicate (base + 2 * S nesting) ' ' else gap
      deeper = case token.kind of
        OpenParen => S nesting
        CloseParen => minus nesting 1
        _ => nesting
   in spacing ++ original ++ wrapTokens points newline deeper base (Just token) token.span.finish.offset remaining rest

wrapApplications : String -> ParsedDocument -> String
wrapApplications source document = case newlineStyle False False (unpack source) of
  Nothing => source
  Just newline =>
    let proposed = pack (wrapTokens (breakpoints document) newline 0 0 Nothing 0 (unpack source) document.tokens)
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
  let formatted = pack (formatTokens Nothing 0 (unpack source) original.tokens)
  if byteCount formatted > 65536 then Left FormatSizeLimit else Right ()
  candidate <- case parseDocument 64 256 formatted of
    Left _ => Left FormatShapeChanged
    Right document => Right document
  if sameDocumentShape original candidate then Right (wrapApplications formatted candidate) else Left FormatShapeChanged
