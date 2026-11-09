-- File/project adapters around checked core-to-C emission.
module Fibril.Driver.Native

import public Fibril.Driver.Native.Emit
import Fibril.Core.Term
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
emitBinaryCFile : String -> IO (Either String String)
emitBinaryCFile path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (renderFileError path (show err))
    Right source => case resolveSource source of
      Left err => Left (renderDriverError path source (FrontendFailure err))
      Right term => emitCheckedBinaryC 4096 8388608 term

public export
emitBinaryCProject : String -> String -> IO (Either String String)
emitBinaryCProject root entry = do
  checked <- checkProject root entry
  pure $ case checked of
    Left err => Left (renderGraphError err)
    Right project => emitCheckedBinaryCGlobals project.globals 4096 8388608 project.term

public export
emitCProject : String -> String -> IO (Either String String)
emitCProject root entry = do
  checked <- checkProject root entry
  pure $ case checked of
    Left err => Left (renderGraphError err)
    Right project => emitCheckedCGlobals project.globals project.term

public export
emitCPackage : String -> IO (Either String String)
emitCPackage manifest = do
  checked <- checkPackage manifest
  pure $ case checked of
    Left err => Left (renderGraphError err)
    Right project => emitCheckedCGlobals project.globals project.term

public export
emitEmbeddedCFile : String -> IO (Either String String)
emitEmbeddedCFile path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (renderFileError path (show err))
    Right source => case resolveSource source of
      Left err => Left (renderDriverError path source (FrontendFailure err))
      Right term => emitCheckedEmbeddedC term

public export
emitEmbeddedCProject : String -> String -> IO (Either String String)
emitEmbeddedCProject root entry = do
  checked <- checkProject root entry
  pure $ case checked of
    Left err => Left (renderGraphError err)
    Right project => emitCheckedEmbeddedCGlobals project.globals project.term

public export
emitEmbeddedCPackage : String -> IO (Either String String)
emitEmbeddedCPackage manifest = do
  checked <- checkPackage manifest
  pure $ case checked of
    Left err => Left (renderGraphError err)
    Right project => emitCheckedEmbeddedCGlobals project.globals project.term

public export
emitNetworkCFile : String -> IO (Either String String)
emitNetworkCFile path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (renderFileError path (show err))
    Right source => case resolveSource source of
      Left err => Left (renderDriverError path source (FrontendFailure err))
      Right term => emitCheckedNetworkC term

public export
emitNetworkCProject : String -> String -> IO (Either String String)
emitNetworkCProject root entry = do
  checked <- checkProject root entry
  pure $ case checked of
    Left err => Left (renderGraphError err)
    Right project => emitCheckedNetworkCGlobals project.globals project.term

public export
emitNetworkCPackage : String -> IO (Either String String)
emitNetworkCPackage manifest = do
  checked <- checkPackage manifest
  pure $ case checked of
    Left err => Left (renderGraphError err)
    Right project => emitCheckedNetworkCGlobals project.globals project.term
