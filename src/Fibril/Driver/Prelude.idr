-- Parse and check actual Fibril library definitions, then expose closed globals.
module Fibril.Driver.Prelude

import Data.List
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Runtime
import Fibril.Source.Syntax
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Parser
import Fibril.Source.Declaration
import Fibril.Source.Resolve
import Fibril.Source.Global
import Fibril.Source.Primitive
import Fibril.Driver.PreludeSource

import Fibril.Driver.Limits

%default total

install : List GlobalDefinition -> List Declaration -> Either String (List GlobalDefinition)
install globals [] = Right globals
install globals (decl :: rest) = do
  if decl.quantity /= Unrestricted
     then Left "Bundled globals must be closed unrestricted definitions"
     else Right ()
  expected <- case resolveClosedWith globals decl.expected of
    Left err => Left (show err)
    Right term => Right term
  value <- case resolveClosedWith globals decl.value of
    Left err => Left (show err)
    Right term => Right term
  _ <- case checkRuntime checkingDepth typeReductionFuel Empty value expected of
    Left err => Left (show err)
    Right checked => Right checked
  install (Global decl.name expected value :: globals) rest

||| The bundled source is still parsed/resolved/core-checked, not installed as axioms.
||| Globals are closed and unrestricted; this is not a module/package loader.
public export
preludeGlobals : Either String (List GlobalDefinition)
preludeGlobals = do
  tokens <- case lexSource preludeSource of
    Left err => Left (show err)
    Right tokens => Right tokens
  declarations <- case parseDeclarations 64 256
      (advancePosition (At 0 1 1) (unpack preludeSource)) tokens of
    Left err => Left (show err)
    Right declarations => Right declarations
  install primitiveGlobals declarations
