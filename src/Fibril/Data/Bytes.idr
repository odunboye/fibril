-- Immutable host-side byte values; not yet a Fibril source/core type.
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

export
Eq Bytes where
  Packed left == Packed right = left == right
