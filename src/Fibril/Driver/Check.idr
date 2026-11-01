-- Orchestrate the expression frontend; core checking remains independent.
module Fibril.Driver.Check

import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Parser
import Fibril.Source.Resolve
import Fibril.Source.File
import Fibril.Source.Diagnostic
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

||| Preserve located frontend failures until the driver chooses a presentation.
||| Core/evaluation failures remain unlocated rather than acquiring invented spans.
public export
data DriverError
  = FrontendFailure FrontendError
  | ErasedFailure CheckError
  | RuntimeFailure RuntimeError
  | EvaluationLimit
  | PostReductionFailure RuntimeError

public export
Show DriverError where
  show (FrontendFailure err) = show err
  show (ErasedFailure err) = "Erased checking: " ++ show err
  show (RuntimeFailure err) = "Runtime checking: " ++ show err
  show EvaluationLimit = "Evaluation budget exhausted; no normal form reported"
  show (PostReductionFailure err) = "Post-reduction checking failed: " ++ show err

frontendPoint : FrontendError -> Maybe Diagnostic
frontendPoint (Parsing err) = Just (AtPoint err.position ("Parsing: " ++ err.message))
frontendPoint (Resolving err) =
  Just (AtPoint err.position ("Resolution: Unbound name " ++ show err.name))
frontendPoint (Lexical (UnexpectedChar position char)) =
  Just (AtPoint position ("Lexing: Unexpected character " ++ show char))
frontendPoint (Lexical (InvalidSource err)) =
  Just (AtPoint err.position ("Lexing: " ++ show err.problem ++
                             " (code point " ++ show err.codePoint ++ ")"))
frontendPoint (Lexical ScanLimit) = Nothing

||| Contextual file diagnostics without reparsing or assigning core source spans.
public export
renderDriverError : String -> String -> DriverError -> String
renderDriverError path source (FrontendFailure err) =
  case frontendPoint err of
    Just diagnostic => renderDiagnostic path source diagnostic
    Nothing => renderFileError path (show err)
renderDriverError path source err = renderFileError path (show err)

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

prepareTerm : Term 0 -> Either DriverError RuntimeSource
prepareTerm term =
  case inferRuntime 256 128 Empty term of
    Left err => Left (RuntimeFailure err)
    Right checked => Right (PreparedRuntime term checked.inferredType)

||| Structured preparation; resolve and runtime-check exactly once.
public export
prepareRuntimeSourceDetailed : String -> Either DriverError RuntimeSource
prepareRuntimeSourceDetailed source = do
  term <- case resolveSource source of
    Left err => Left (FrontendFailure err)
    Right term => Right term
  prepareTerm term

||| Compatibility presentation for callers that only need a plain error string.
public export
prepareRuntimeSource : String -> Either String RuntimeSource
prepareRuntimeSource source =
  case prepareRuntimeSourceDetailed source of
    Left err => Left (show err)
    Right prepared => Right prepared

||| Structured source checking; no source location is claimed for core failures.
public export
checkSourceDetailed : Bool -> String -> Either DriverError (List String)
checkSourceDetailed erasedOnly source = do
  term <- case resolveSource source of
    Left err => Left (FrontendFailure err)
    Right term => Right term
  if erasedOnly
     then case inferErased 256 128 Empty term of
       Left err => Left (ErasedFailure err)
       Right ty => Right ["Erased checking: accepted (no runtime-use guarantee)",
                          "Type: " ++ renderTerm ty]
     else do
       checked <- prepareTerm term
       Right ["Runtime checking: accepted", "Type: " ++ renderTerm checked.inferredType]

||| Plain source checking preserves its existing single-message API.
public export
checkSource : Bool -> String -> Either String (List String)
checkSource erasedOnly source =
  case checkSourceDetailed erasedOnly source of
    Left err => Left (show err)
    Right lines => Right lines

||| Use the bounded UTF-8 loader and render located errors with original source.
public export
checkFile : Bool -> String -> IO (Either String (List String))
checkFile erasedOnly path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (renderFileError path (show err))
    Right source =>
      case checkSourceDetailed erasedOnly source of
        Left err => Left (renderDriverError path source err)
        Right lines => Right lines
