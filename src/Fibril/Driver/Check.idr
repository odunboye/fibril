-- Orchestrate the expression frontend; core checking remains independent.
module Fibril.Driver.Check

import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Parser
import Fibril.Source.Resolve
import Fibril.Source.File
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Pretty
import Fibril.Core.Erased
import Fibril.Core.Runtime

%default total

||| Preserve the frontend stage when reporting errors.
public export
data FrontendError = Lexical LexError | Parsing ParseError | Resolving ResolveError

public export
Show FrontendError where
  show (Lexical err) = "Lexing: " ++ show err
  show (Parsing err) = "Parsing: " ++ show err
  show (Resolving err) = "Resolution: " ++ show err

||| Parse and resolve a single closed expression with a fixed prototype budget.
||| This is not declaration elaboration, implicit inference, or module loading.
public export
resolveSource : String -> Either FrontendError (Term 0)
resolveSource source = do
  tokens <- case lexSource source of
    Left err => Left (Lexical err)
    Right tokens => Right tokens
  syntax <- case parseExpression 256 (advancePosition (At 0 1 1) (unpack source)) tokens of
    Left err => Left (Parsing err)
    Right syntax => Right syntax
  case resolveClosed syntax of
    Left err => Left (Resolving err)
    Right term => Right term

||| Prepared diagnostic data, not an unforgeable kernel certificate.
public export
record RuntimeSource where
  constructor PreparedRuntime
  term : Term 0
  inferredType : Term 0

prepareTerm : Term 0 -> Either String RuntimeSource
prepareTerm term =
  case inferRuntime 256 128 Empty term of
    Left err => Left ("Runtime checking: " ++ show err)
    Right checked => Right (PreparedRuntime term checked.inferredType)

||| Resolve and runtime-check once for drivers that need the actual core term.
public export
prepareRuntimeSource : String -> Either String RuntimeSource
prepareRuntimeSource source = do
  term <- case resolveSource source of
    Left err => Left (show err)
    Right term => Right term
  prepareTerm term

||| Check an expression in erased-only mode or ordinary runtime mode.
||| Successful diagnostics explicitly identify the mode; neither compiles code.
public export
checkSource : (erasedOnly : Bool) -> String -> Either String (List String)
checkSource erasedOnly source = do
  term <- case resolveSource source of
    Left err => Left (show err)
    Right term => Right term
  if erasedOnly
     then case inferErased 256 128 Empty term of
       Left err => Left ("Erased checking: " ++ show err)
       Right ty => Right ["Erased checking: accepted (no runtime-use guarantee)",
                          "Type: " ++ renderTerm ty]
     else do
       checked <- prepareTerm term
       Right ["Runtime checking: accepted", "Type: " ++ renderTerm checked.inferredType]

||| Use the bounded UTF-8 loader before frontend/checker processing.
public export
checkFile : Bool -> String -> IO (Either String (List String))
checkFile erasedOnly path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (show err)
    Right source => checkSource erasedOnly source
