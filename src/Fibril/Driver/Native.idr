-- File/project adapters around checked core-to-C emission.
module Fibril.Driver.Native

import public Fibril.Driver.Native.Emit
import Fibril.Source.File
import Fibril.Source.Diagnostic
import Fibril.Driver.Check
import Fibril.Driver.ModuleCheck
import Fibril.Driver.ModuleGraph

%default total

public export
emitCFile : String -> IO (Either String String)
emitCFile path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (renderFileError path (show err))
    Right source => case resolveSource source of
      Left err => Left (renderDriverError path source (FrontendFailure err))
      Right term => emitCheckedC term

public export
emitCProject : String -> String -> IO (Either String String)
emitCProject root entry = do
  checked <- checkProject root entry
  pure $ case checked of
    Left err => Left (renderGraphError err)
    Right project => emitCheckedC project.term

public export
emitCPackage : String -> IO (Either String String)
emitCPackage manifest = do
  checked <- checkPackage manifest
  pure $ case checked of
    Left err => Left (renderGraphError err)
    Right project => emitCheckedC project.term
