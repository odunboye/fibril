module Tests.Lock

import Fibril.Project.Lock

%default total

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
  ]
