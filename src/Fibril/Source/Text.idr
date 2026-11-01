-- Validation of already-decoded source text, not UTF-8 decoding or tokenization.
module Fibril.Source.Text

%default total

||| One-based logical line/column; zero-based Unicode-scalar offset.
||| Tabs count as one column. CRLF consumes two offsets and one line break.
public export
record Position where
  constructor At
  offset : Nat
  line : Nat
  column : Nat

public export
Show Position where
  show position = show position.line ++ ":" ++ show position.column

||| Advance over a complete text chunk without validating it.
||| CRLF must be supplied together; splitting the pair across calls counts two
||| line breaks. Tokenization preserves this invariant for whitespace chunks.
public export
advancePosition : Position -> List Char -> Position
advancePosition at [] = at
advancePosition at ('\r' :: '\n' :: rest) =
  advancePosition (At (at.offset + 2) (S at.line) 1) rest
advancePosition at (char :: rest) =
  if char == '\n' || char == '\r'
     then advancePosition (At (S at.offset) (S at.line) 1) rest
     else advancePosition (At (S at.offset) at.line (S at.column)) rest

||| Conservative source-wide rejection categories, independent of token context.
public export
data TextProblem = InvalidScalar | ControlCharacter | BidiControl | ByteOrderMark

public export
Show TextProblem where
  show InvalidScalar = "Invalid Unicode scalar"
  show ControlCharacter = "Unsupported source control character"
  show BidiControl = "Raw bidirectional formatting control is not allowed"
  show ByteOrderMark = "Byte order marks are not allowed"

||| The rejected scalar's position and reason; no source text is modified.
public export
record TextError where
  constructor Rejected
  position : Position
  problem : TextProblem
  codePoint : Int

public export
Show TextError where
  show err = show err.position ++ ": " ++ show err.problem ++
             " (code point " ++ show err.codePoint ++ ")"

problemAt : Char -> Maybe TextProblem
problemAt char =
  let cp = ord char
   in if cp < 0 || cp > 0x10FFFF || (cp >= 0xD800 && cp <= 0xDFFF)
         then Just InvalidScalar
      else if cp == 0xFEFF
         then Just ByteOrderMark
      else if cp == 0x061C || cp == 0x200E || cp == 0x200F ||
              (cp >= 0x202A && cp <= 0x202E) || (cp >= 0x2066 && cp <= 0x2069)
         then Just BidiControl
      else if (cp < 0x20 && char /= '\n' && char /= '\r' && char /= '\t') ||
              (cp >= 0x7F && cp <= 0x9F) || cp == 0x2028 || cp == 0x2029
         then Just ControlCharacter
      else Nothing

walk : Position -> List Char -> Either TextError ()
walk position [] = Right ()
walk position ('\r' :: '\n' :: rest) =
  walk (advancePosition position ['\r', '\n']) rest
walk position (char :: rest) =
  case problemAt char of
    Just problem => Left (Rejected position problem (ord char))
    Nothing => walk (advancePosition position [char]) rest

||| Validate decoded text, returning its original spelling unchanged.
||| Allows Unicode prose/emoji/joiners; this does not approve them as identifiers.
||| Rejects raw bidi controls even inside comments/strings under initial policy.
||| No normalization, confusable detection, or byte-decoding guarantee is implied.
public export
validateText : String -> Either TextError String
validateText source = do
  walk (At 0 1 1) (unpack source)
  Right source
