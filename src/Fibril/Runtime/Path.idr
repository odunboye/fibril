-- POSIX filesystem identity for the bootstrap compiler, not a Fibril FFI.
module Fibril.Runtime.Path

import System.FFI

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
