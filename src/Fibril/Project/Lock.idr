||| Pure core of fibril.lock (docs/lockfile.md): tree digests, canonical encoding
||| and drift reporting. No filesystem access and no decoder yet.
module Fibril.Project.Lock

import Data.List
import Data.List1
import Data.String
import Fibril.Driver.JSON
import Fibril.Project.Digest
import Fibril.Source.UTF8

%default total

public export
record LockedPackage where
  constructor MkLocked
  name : String
  modulePrefix : String
  path : String
  manifestSha : String
  treeSha : String

public export
record Lock where
  constructor MkLock
  root : String
  foundation : String
  packages : List LockedPackage

nul : String
nul = singleton (chr 0)

||| Paths are '/'-separated and relative to source-dir; anything that could
||| alias another file or escape the tree is rejected, never normalized.
invalidPath : String -> Bool
invalidPath p =
  p == "" || isPrefixOf "/" p || elem (chr 0) (unpack p)
    || any (\part => part == "" || part == "." || part == "..") (forget (split (== '/') p))

hasAdjacentDuplicate : List String -> Bool
hasAdjacentDuplicate (a :: rest@(b :: _)) = a == b || hasAdjacentDuplicate rest
hasAdjacentDuplicate _ = False

||| SHA-256 over the sorted lines `path NUL file-sha256-hex LF`. Raw bytes, so a
||| CRLF checkout changes the digest. Nothing for invalid or duplicate paths.
export
treeDigest : List (String, List Bits8) -> Maybe String
treeDigest files =
  let sorted = sortBy (\a, b => compare (fst a) (fst b)) files
      paths = map fst sorted
   in if any invalidPath paths || hasAdjacentDuplicate paths
        then Nothing
        else map (sha256Hex . concat) (traverse line sorted)
  where
    line : (String, List Bits8) -> Maybe (List Bits8)
    line (p, bytes) = case encodeUTF8 (p ++ nul ++ sha256Hex bytes ++ "\n") of
      Right encoded => Just encoded
      Left _ => Nothing

||| Path from directory `from` to directory `to`, both canonical absolute paths.
export
relativePath : (from, to : String) -> String
relativePath from to =
  let (ups, downs) = strip (components from) (components to)
      parts = map (const "..") ups ++ downs
   in if null parts then "." else joinBy "/" parts
  where
    components : String -> List String
    components p = filter (/= "") (forget (split (== '/') p))

    strip : List String -> List String -> (List String, List String)
    strip (a :: as) (b :: bs) = if a == b then strip as bs else (a :: as, b :: bs)
    strip as bs = (as, bs)

packageJSON : LockedPackage -> String
packageJSON p = jsonObject
  [ ("name", jsonString p.name), ("module-prefix", jsonString p.modulePrefix)
  , ("path", jsonString p.path), ("manifest-sha256", jsonString p.manifestSha)
  , ("tree-sha256", jsonString p.treeSha) ]

||| Canonical text: packages sorted by name, one per line, trailing newline, so
||| equal locks are byte-equal and diffs are per package.
export
encodeLock : Lock -> String
encodeLock lock =
  let sorted = sortBy (\a, b => compare a.name b.name) lock.packages
      body = joinBy ",\n" (map (\p => "    " ++ packageJSON p) sorted)
   in "{\n  \"schema\": 1,\n  \"root\": " ++ jsonString lock.root
        ++ ",\n  \"foundation\": " ++ jsonString lock.foundation
        ++ ",\n  \"packages\": [\n" ++ body ++ "\n  ]\n}\n"

||| Human-readable drift between the recorded lock and the freshly computed one.
||| Empty means the lock verifies.
export
lockDrift : (recorded, current : Lock) -> List String
lockDrift recorded current =
  [ "root package changed: " ++ recorded.root ++ " -> " ++ current.root | recorded.root /= current.root ]
  ++ [ "foundation changed: " ++ recorded.foundation ++ " -> " ++ current.foundation
     | recorded.foundation /= current.foundation ]
  ++ concatMap compareRecorded recorded.packages
  ++ [ "package " ++ p.name ++ ": not in fibril.lock" | p <- current.packages, not (hasName p.name recorded.packages) ]
  where
    hasName : String -> List LockedPackage -> Bool
    hasName n = any (\p => p.name == n)

    compareRecorded : LockedPackage -> List String
    compareRecorded old = case find (\p => p.name == old.name) current.packages of
      Nothing => ["package " ++ old.name ++ ": in fibril.lock but not in the dependency closure"]
      Just new =>
        [ "package " ++ old.name ++ ": manifest changed" | old.manifestSha /= new.manifestSha ]
        ++ [ "package " ++ old.name ++ ": sources changed" | old.treeSha /= new.treeSha ]
        ++ [ "package " ++ old.name ++ ": path or module prefix changed"
           | old.path /= new.path || old.modulePrefix /= new.modulePrefix ]
