-- Strict scalar UTF-8 codec; no replacement decoding or normalization.
-- Encoding reference: RFC 3629, section 4; see docs/unicode-source.md.
module Fibril.Source.UTF8

%default total

||| Malformed byte-sequence categories; offsets identify the lead or bad byte.
public export
data UTF8Problem
  = InvalidLead
  | InvalidContinuation
  | TruncatedSequence
  | OverlongEncoding
  | SurrogateEncoding
  | ScalarOutOfRange

public export
Show UTF8Problem where
  show InvalidLead = "Invalid UTF-8 leading byte"
  show InvalidContinuation = "Invalid UTF-8 continuation byte"
  show TruncatedSequence = "Truncated UTF-8 sequence"
  show OverlongEncoding = "Overlong UTF-8 encoding"
  show SurrogateEncoding = "UTF-8 encoded surrogate"
  show ScalarOutOfRange = "UTF-8 scalar exceeds U+10FFFF"

||| A zero-based byte offset, distinct from decoded scalar/editor positions.
public export
record UTF8Error where
  constructor Malformed
  byteOffset : Nat
  problem : UTF8Problem

public export
Show UTF8Error where
  show err = "byte " ++ show err.byteOffset ++ ": " ++ show err.problem

continuations : Nat -> List Bits8 -> Either UTF8Error ()
continuations offset [] = Right ()
continuations offset (byte :: rest) =
  if byte >= 0x80 && byte <= 0xBF
     then continuations (S offset) rest
     else Left (Malformed offset InvalidContinuation)

-- Continuations have already been validated. Arithmetic cannot exceed 0x1FFFFF.
payload : Bits8 -> Int
payload byte = cast byte - 0x80

decode : Nat -> List Bits8 -> Either UTF8Error (List Char)
decode offset [] = Right []
decode offset (a :: rest) =
  let lead : Int = cast a
   in if a < 0x80
         then map (chr lead ::) (decode (S offset) rest)
      else if a >= 0xC2 && a <= 0xDF
         then case rest of
           b :: tail => do
             continuations (S offset) [b]
             let scalar = (lead - 0xC0) * 64 + payload b
             map (chr scalar ::) (decode (offset + 2) tail)
           _ => Left (Malformed offset TruncatedSequence)
      else if a >= 0xE0 && a <= 0xEF
         then case rest of
           b :: c :: tail => do
             continuations (S offset) [b, c]
             let scalar = (lead - 0xE0) * 4096 + payload b * 64 + payload c
             if scalar < 0x800
                then Left (Malformed offset OverlongEncoding)
                else if scalar >= 0xD800 && scalar <= 0xDFFF
                        then Left (Malformed offset SurrogateEncoding)
                        else map (chr scalar ::) (decode (offset + 3) tail)
           _ => Left (Malformed offset TruncatedSequence)
      else if a >= 0xF0 && a <= 0xF4
         then case rest of
           b :: c :: d :: tail => do
             continuations (S offset) [b, c, d]
             let scalar = (lead - 0xF0) * 262144 + payload b * 4096 + payload c * 64 + payload d
             if scalar < 0x10000
                then Left (Malformed offset OverlongEncoding)
                else if scalar > 0x10FFFF
                        then Left (Malformed offset ScalarOutOfRange)
                        else map (chr scalar ::) (decode (offset + 4) tail)
           _ => Left (Malformed offset TruncatedSequence)
      else Left (Malformed offset InvalidLead)

encodeScalar : Nat -> Char -> Either UTF8Error (List Bits8)
encodeScalar offset char =
  let n = ord char in
    if n < 0 || n > 0x10FFFF then Left (Malformed offset ScalarOutOfRange)
    else if n >= 0xD800 && n <= 0xDFFF then Left (Malformed offset SurrogateEncoding)
    else Right (map cast (if n < 128 then [n]
      else if n < 2048 then [192 + div n 64, 128 + mod n 64]
      else if n < 65536 then [224 + div n 4096, 128 + mod (div n 64) 64, 128 + mod n 64]
      else [240 + div n 262144, 128 + mod (div n 4096) 64, 128 + mod (div n 64) 64, 128 + mod n 64]))

encodeScalars : Nat -> List Char -> Either UTF8Error (List Bits8)
encodeScalars offset [] = Right []
encodeScalars offset (char :: rest) = do
  encoded <- encodeScalar offset char
  suffix <- encodeScalars (offset + length encoded) rest
  Right (encoded ++ suffix)

||| Encode scalar text without normalization or NUL filtering. Invalid trusted
||| host characters fail; the error offset is the encoded valid-prefix length.
public export
encodeUTF8 : String -> Either UTF8Error (List Bits8)
encodeUTF8 = encodeScalars 0 . unpack

||| Decode shortest-form UTF-8 scalar sequences, or report a malformed sequence.
||| Valid U+FFFD is preserved; it is never inserted to conceal invalid bytes.
||| Text controls/BOM policy is handled separately by Source.Text.
public export
decodeUTF8 : List Bits8 -> Either UTF8Error String
decodeUTF8 bytes = map pack (decode 0 bytes)
