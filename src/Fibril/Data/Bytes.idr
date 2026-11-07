-- Immutable host representation for checked core/source byte values.
module Fibril.Data.Bytes

import Data.List

%default total

-- Hide representation; no mutable buffer or pointer is exposed.
export
data Bytes = Packed (List Bits8)

export
fromList : List Bits8 -> Bytes
fromList = Packed

export
toList : Bytes -> List Bits8
toList (Packed bytes) = bytes

export
empty : Bytes
empty = Packed []

export
byteLength : Bytes -> Nat
byteLength (Packed bytes) = length bytes

export
append : Bytes -> Bytes -> Bytes
append (Packed left) (Packed right) = Packed (left ++ right)

||| A bounded slice; indices beyond the end produce empty bytes.
export
slice : Nat -> Nat -> Bytes -> Bytes
slice start count (Packed bytes) = Packed (take count (drop start bytes))

||| Missing indices are explicit, including every index into empty bytes.
export
byteAt : Nat -> Bytes -> Maybe Bits8
byteAt index (Packed bytes) = at index bytes
  where
    at : Nat -> List Bits8 -> Maybe Bits8
    at _ [] = Nothing
    at Z (byte :: _) = Just byte
    at (S n) (_ :: rest) = at n rest

export
Eq Bytes where
  Packed left == Packed right = left == right
