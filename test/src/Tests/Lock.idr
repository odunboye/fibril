module Tests.Lock

import Data.List
import Data.String
import Fibril.Project.Lock
import Fibril.Project.LockDecode

%default total

sha : Char -> String
sha c = pack (replicate 64 c)

hexLock : Lock
hexLock = MkLock "app\"x" "de-morgan"
  [ MkLocked "core" "Email" "../core" (sha 'a') (sha 'b')
  , MkLocked "ma\\il\n" "Mail" "../mail" (sha '0') (sha 'f') ]

good : String
good = encodeLock hexLock

mapLines : (String -> String) -> String -> String
mapLines f text = unlines (map f (lines text))

isPackageLine : String -> Bool
isPackageLine = isPrefixOf "    {"

dropS : Nat -> String -> String
dropS n s = pack (drop n (unpack s))

dropLast : String -> String
dropLast s = pack (reverse (drop 1 (reverse (unpack s))))

swapPackages : String -> String
swapPackages text = case lines text of
  (a :: b :: c :: d :: e :: p1 :: p2 :: rest) => unlines (a :: b :: c :: d :: e :: (p2 ++ ",") :: dropLast p1 :: rest)
  other => unlines other

rejected : String -> Bool
rejected text = case decodeLock text of Left _ => True; Right _ => False

bytes : String -> List Bits8
bytes s = map (cast . ord) (unpack s)

pkg : String -> String -> String -> LockedPackage
pkg n m t = MkLocked n "P" ("../" ++ n) m t

base : Lock
base = MkLock "app" "de-morgan" [pkg "core" "m1" "t1", pkg "mail" "m2" "t2"]

-- Reference digests computed independently with Python hashlib.
export
checks : List (String, Bool)
checks =
  [ ("tree digest of one file matches the independent reference",
      treeDigest [("a.fib", bytes "x")] == Just "e3455ef3034cd936be3904540082709e7243fcc2c05c2f2bbbdd8728de5c135a")
  , ("tree digest sorts by path and matches the independent reference",
      treeDigest [("b/c.fib", bytes "y"), ("a.fib", bytes "x")]
        == Just "50a7f6254cfbf2686fd257d4f627fdc546e464da11b9041cf440dc06953bfbfc")
  , ("empty tree digests the empty input",
      treeDigest [] == Just "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
  , ("tree digest sees content and path changes",
      treeDigest [("a.fib", bytes "x")] /= treeDigest [("a.fib", bytes "z")]
        && treeDigest [("a.fib", bytes "x")] /= treeDigest [("b.fib", bytes "x")])
  , ("raw bytes: a CRLF file digests differently",
      treeDigest [("a.fib", bytes "x\n")] /= treeDigest [("a.fib", bytes "x\r\n")])
  , ("duplicate, empty, absolute, dot and NUL paths are rejected",
      treeDigest [("a.fib", []), ("a.fib", [])] == Nothing && treeDigest [("", [])] == Nothing
        && treeDigest [("/a.fib", [])] == Nothing && treeDigest [("../a.fib", [])] == Nothing
        && treeDigest [("a//b.fib", [])] == Nothing && treeDigest [("a\NULb", [])] == Nothing)
  , ("encoding is canonical regardless of package order",
      encodeLock base == encodeLock ({ packages := reverse base.packages } base))
  , ("encoding has the documented shape",
      encodeLock (MkLock "app" "de-morgan" [MkLocked "core" "Email" "../core" "m" "t"])
        == "{\n  \"schema\": 1,\n  \"root\": \"app\",\n  \"foundation\": \"de-morgan\",\n  \"packages\": [\n"
           ++ "    {\"name\":\"core\",\"module-prefix\":\"Email\",\"path\":\"../core\",\"manifest-sha256\":\"m\",\"tree-sha256\":\"t\"}\n  ]\n}\n")
  , ("identical locks have no drift", lockDrift base base == [])
  , ("source drift names the package",
      lockDrift base ({ packages := [pkg "core" "m1" "tX", pkg "mail" "m2" "t2"] } base)
        == ["package core: sources changed"])
  , ("manifest drift names the package",
      lockDrift base ({ packages := [pkg "core" "mX" "t1", pkg "mail" "m2" "t2"] } base)
        == ["package core: manifest changed"])
  , ("added and removed packages are drift, not warnings",
      lockDrift base ({ packages := [pkg "core" "m1" "t1", pkg "new" "m" "t"] } base)
        == [ "package mail: in fibril.lock but not in the dependency closure"
           , "package new: not in fibril.lock" ])
  , ("foundation and root changes are drift",
      length (lockDrift base (MkLock "other" "x" base.packages)) == 2)
  , ("decode round-trips a lock with quotes, backslashes and control characters",
      case decodeLock good of
        Right lock => encodeLock lock == good && lock.root == "app\"x"
                      && map (.name) lock.packages == ["core", "ma\\il\n"]
        Left _ => False)
  , ("decode rejects schema 2",
      rejected ("{\n  \"schema\": 2," ++ dropS (length "{\n  \"schema\": 1,") good))
  , ("decode rejects unknown keys, extra whitespace and trailing data",
      rejected (mapLines (\l => if isPackageLine l then "    {\"nme\":" ++ dropS (length "    {\"name\":") l else l) good)
        && rejected (mapLines (\l => if isPackageLine l then "    { " ++ dropS 5 l else l) good)
        && rejected (good ++ "x") && rejected (good ++ "\n") && rejected ("\r" ++ good))
  , ("decode rejects missing or extra commas and reordered packages",
      rejected (mapLines (\l => if isPackageLine l && isSuffixOf "," l then dropLast l else l) good)
        && rejected (mapLines (\l => if isPackageLine l && not (isSuffixOf "," l) then l ++ "," else l) good)
        && rejected (swapPackages good))
  , ("decode rejects non-hex or short digests and duplicate names",
      rejected (encodeLock (MkLock "a" "f" [MkLocked "c" "P" "p" "m1" (sha 'b')]))
        && rejected (encodeLock (MkLock "a" "f" [MkLocked "c" "P" "p" (sha 'A') (sha 'b')]))
        && rejected (encodeLock (MkLock "a" "f" [MkLocked "c" "P" "p" (sha 'a') (sha 'b'), MkLocked "c" "Q" "q" (sha 'a') (sha 'b')])))
  , ("decode rejects empty, truncated and non-lock input",
      rejected "" && rejected "{}" && rejected (substr 0 40 good) && rejected "not json")
  ]
