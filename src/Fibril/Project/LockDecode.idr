||| Strict reader for fibril.lock. It parses only the exact layout `encodeLock`
||| writes, then requires the re-encoding to equal the input. That single
||| equality rejects unknown or duplicate keys, reordering, extra whitespace, a
||| different schema and trailing data, so a lock is never half-trusted.
module Fibril.Project.LockDecode

import Data.List
import Data.Maybe
import Data.String
import Fibril.Project.Lock

%default total

hexValue : Char -> Maybe Int
hexValue c =
  if c >= '0' && c <= '9' then Just (ord c - ord '0')
  else if c >= 'a' && c <= 'f' then Just (ord c - ord 'a' + 10)
  else Nothing

||| A JSON string using only the escapes the encoder emits: \" \\ and \u00XX below 0x20.
scanString : List Char -> Maybe (String, List Char)
scanString ('"' :: rest) = go rest []
  where
    go : List Char -> List Char -> Maybe (String, List Char)
    go [] _ = Nothing
    go ('"' :: r) acc = Just (pack (reverse acc), r)
    go ('\\' :: '"' :: r) acc = go r ('"' :: acc)
    go ('\\' :: '\\' :: r) acc = go r ('\\' :: acc)
    go ('\\' :: 'u' :: '0' :: '0' :: h :: l :: r) acc = do
      hv <- hexValue h
      lv <- hexValue l
      if hv * 16 + lv < 32 then go r (chr (hv * 16 + lv) :: acc) else Nothing
    go ('\\' :: _) _ = Nothing
    go (c :: r) acc = go r (c :: acc)
scanString _ = Nothing

dropLiteral : String -> List Char -> Maybe (List Char)
dropLiteral lit cs = go (unpack lit) cs
  where
    go : List Char -> List Char -> Maybe (List Char)
    go [] rest = Just rest
    go (l :: ls) (c :: rest) = if l == c then go ls rest else Nothing
    go _ [] = Nothing

stringField : String -> List Char -> Maybe (String, List Char)
stringField key cs = dropLiteral key cs >>= scanString

isSha : String -> Bool
isSha s = length s == 64 && all (\c => isJust (hexValue c)) (unpack s)

parsePackage : String -> Maybe LockedPackage
parsePackage line = do
  rest <- dropLiteral "    " (unpack line)
  let body = case reverse rest of
               (',' :: r) => reverse r
               _ => rest
  (name, r1) <- stringField "{\"name\":" body
  (pfx, r2) <- stringField ",\"module-prefix\":" r1
  (path, r3) <- stringField ",\"path\":" r2
  (manifest, r4) <- stringField ",\"manifest-sha256\":" r3
  (tree, r5) <- stringField ",\"tree-sha256\":" r4
  if r5 == ['}'] && isSha manifest && isSha tree
    then Just (MkLocked name pfx path manifest tree)
    else Nothing

hasDuplicateName : List LockedPackage -> Bool
hasDuplicateName ps = go (sort (map (.name) ps))
  where
    go : List String -> Bool
    go (a :: rest@(b :: _)) = a == b || go rest
    go _ = False

||| Left explains why the file must not be trusted.
export
decodeLock : String -> Either String Lock
decodeLock text = case lines text of
  ("{" :: "  \"schema\": 1," :: rootLine :: foundationLine :: "  \"packages\": [" :: rest) =>
    let (packageLines, closing) = break (== "  ]") rest
     in case ( stringField "  \"root\": " (unpack rootLine)
             , stringField "  \"foundation\": " (unpack foundationLine)
             , traverse parsePackage packageLines ) of
          (Just (root, [',']), Just (foundation, [',']), Just packages) =>
            let lock = MkLock root foundation packages
             in if closing /= ["  ]", "}"] || hasDuplicateName packages
                  then Left "fibril.lock is malformed"
                  else if encodeLock lock == text
                    then Right lock
                    else Left "fibril.lock is not in canonical form"
          _ => Left "fibril.lock is malformed"
  _ => Left "fibril.lock is malformed"
