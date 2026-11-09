module Fibril.Driver.JavaScript

import public Fibril.Driver.JavaScript.Emit
import Fibril.Core.Term
import Fibril.Source.File
import Fibril.Source.Diagnostic
import Fibril.Driver.Check
import Fibril.Driver.ModuleCheck
import Fibril.Driver.ModuleGraph

%default total

public export
emitJSFile : String -> IO (Either String String)
emitJSFile path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (renderFileError path (show err))
    Right source => case resolveSource source of
      Left err => Left (renderDriverError path source (FrontendFailure err))
      Right term => emitCheckedJS term

public export
emitJSProject : String -> String -> IO (Either String String)
emitJSProject root entry = do
  checked <- checkProject root entry
  pure $ case checked of
    Left err => Left (renderGraphError err)
    Right project => emitCheckedJSGlobals project.globals project.term

public export
emitJSPackage : String -> IO (Either String String)
emitJSPackage manifest = do
  checked <- checkPackage manifest
  pure $ case checked of
    Left err => Left (renderGraphError err)
    Right project => emitCheckedJSGlobals project.globals project.term
