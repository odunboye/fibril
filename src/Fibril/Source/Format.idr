-- Conservative whitespace formatting. Preserve all trivia outside horizontal gaps.
module Fibril.Source.Format

import Data.List
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Document
import Fibril.Source.Shape

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
  if sameDocumentShape original candidate then Right formatted else Left FormatShapeChanged
