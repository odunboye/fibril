-- POSIX filesystem identity for the bootstrap compiler, not a Fibril FFI.
module Fibril.Runtime.Path

import System.FFI
import System.Directory
import Data.List
import Data.List1
import Data.String

%default total

%foreign "C:realpath,libc 6,stdlib.h"
primRealPath : String -> AnyPtr -> PrimIO (Ptr String)

||| Canonicalize an existing path without changing the process working directory.
||| realpath allocates when passed NULL; copy then free using the host FFI helpers.
||| POSIX bootstrap only. This is not an atomic filesystem/sandbox guarantee.
public export
canonicalPath : String -> IO (Maybe String)
canonicalPath path = do
  result <- primIO (primRealPath path prim__getNullAnyPtr)
  if prim__nullPtr result /= 0 then pure Nothing else do
    let text = prim__getString result
    free (prim__forgetPtr result)
    pure (Just text)

public export
joinPath : String -> String -> String
joinPath root name = root ++ (if root == "/" then "" else "/") ++ name

public export
inside : String -> String -> Bool
inside root path = root == path || isPrefixOf (unpack (joinPath root "")) (unpack path)

public export
parentPath : String -> String
parentPath path = let parent = concat (intersperse "/" (reverse (drop 1 (reverse (forget (split (== '/') path))))))
                   in if parent == "" then (case unpack path of '/' :: _ => "/"; _ => ".") else parent

scanDirectory : Nat -> Directory -> String -> IO (Either String Bool)
scanDirectory budget directory wanted = do
  result <- nextDirEntry directory
  case result of
    Left err => pure (Left (show err))
    Right Nothing => pure (Right False)
    Right (Just name) => case budget of
      Z => pure (Left "Directory lookup entry budget exceeded (4096)")
      S rest => if name == wanted then pure (Right True) else scanDirectory rest directory wanted

public export
exactEntry : String -> String -> IO (Either String ())
exactEntry directory wanted = do
  Right handle <- openDir directory
    | Left err => pure (Left (show err))
  result <- scanDirectory 4096 handle wanted
  closeDir handle
  pure $ case result of
    Left err => Left ("Cannot perform exact-case lookup: " ++ err)
    Right False => Left ("Missing exact-case path component " ++ show wanted)
    Right True => Right ()

walkExact : String -> List String -> IO (Either String String)
walkExact directory [] = pure (Right directory)
walkExact directory (component :: rest) =
  if component == "" || component == "." then walkExact directory rest else do
    valid <- if component == ".." then pure (Right ()) else exactEntry directory component
    case valid of
      Left err => pure (Left err)
      Right () => do
        Just next <- canonicalPath (joinPath directory component)
          | Nothing => pure (Left ("Cannot canonicalize path component " ++ show component))
        walkExact next rest

||| Resolve every supplied component with exact spelling, including on a
||| case-insensitive filesystem. Does not pin directories against mutation.
public export
exactCanonical : String -> IO (Either String String)
exactCanonical path = case unpack path of
  [] => pure (Left "Empty path")
  '/' :: _ => walkExact "/" (forget (split (== '/') path))
  _ => do
    Just cwd <- currentDir | Nothing => pure (Left "Cannot obtain current directory")
    walkExact cwd (forget (split (== '/') path))
