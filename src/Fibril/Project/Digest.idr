||| SHA-256 content digests for the planned fibril.lock (docs/lockfile.md).
||| Uses the collection-pinned `sha` package; hashes detect changed content and
||| say nothing about who wrote it.
module Fibril.Project.Digest

import Data.Vect
import Data.Cryptography.Hash
import Data.Cryptography.Hash.SHA

%default total

hexDigit : Bits8 -> Char
hexDigit n = let v = the Int (cast n) in if v < 10 then chr (48 + v) else chr (87 + v)

hexByte : Bits8 -> List Char
hexByte b = [hexDigit (b `div` 16), hexDigit (b `mod` 16)]

||| Lowercase 64-character hex SHA-256 of the exact bytes.
||| shortcut: one-shot over a List Bits8 (the library's interface), fine for source
||| files, slow for very large inputs; upgrade to a Buffer-based update loop if needed.
export
sha256Hex : List Bits8 -> String
sha256Hex bytes =
  let digest = sha256.finalizeHash (sha256.appendHash bytes sha256.mkHashCtx)
   in pack (concatMap hexByte (toList digest))
