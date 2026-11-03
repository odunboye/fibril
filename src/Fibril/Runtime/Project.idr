-- POSIX bootstrap creation, not a Fibril FFI or filesystem sandbox.
-- Call with validated names/fixed relative paths in a trusted working directory.
module Fibril.Runtime.Project

import System.FFI

%default total

%foreign "C:mkdir,libc 6,sys/stat.h"
primMkdir : String -> Int -> PrimIO Int

%foreign "C:fopen,libc 6,stdio.h"
primOpen : String -> String -> PrimIO AnyPtr

%foreign "C:fputs,libc 6,stdio.h"
primPut : String -> AnyPtr -> PrimIO Int

%foreign "C:fclose,libc 6,stdio.h"
primClose : AnyPtr -> PrimIO Int

||| Atomic fresh-directory admission; EEXIST (including symlinks) is failure.
||| 0700 is deliberate; do not expose a partly generated project to other users.
public export
freshDirectory : String -> IO (Either String ())
freshDirectory path = do
  result <- primIO (primMkdir path 448)
  pure (if result == 0 then Right () else
    Left ("Could not create directory " ++ path ++ "; it must be absent and its parent writable."))

||| C11/POSIX exclusive create, never truncate. Close on represented write failures
||| and check buffered close failures. A failed write can leave a partial file.
||| Path components are not descriptor-pinned: hostile concurrent mutation is out
||| of scope. Never pass arbitrary remote-template paths or embedded NULs here.
public export
freshFile : String -> String -> IO (Either String ())
freshFile path contents = do
  file <- primIO (primOpen path "wx")
  if prim__nullAnyPtr file /= 0
     then pure (Left ("Could not exclusively create file " ++ path))
     else do
       written <- primIO (primPut contents file)
       closed <- primIO (primClose file)
       pure (if written < 0 then Left ("Could not finish writing file " ++ path)
             else if closed /= 0 then Left ("Could not finish closing file " ++ path)
             else Right ())
