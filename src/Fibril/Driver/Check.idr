-- Ordinary source checking with a checked Fibril prelude; no console-name parser.
module Fibril.Driver.Check

import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Parser
import Fibril.Source.Declaration
import Fibril.Source.Document
import Fibril.Source.StringLiteral
import Fibril.Source.Resolve
import Fibril.Source.Global
import Fibril.Source.File
import Fibril.Source.Diagnostic
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Pretty
import Fibril.Core.Reduction
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Driver.Prelude
import Fibril.Driver.Console

import Fibril.Driver.Limits

%default total

public export
data FrontendError = Lexical LexError | Parsing ParseError | Resolving ResolveError
                   | PreludeUnavailable String

public export
Show FrontendError where
  show (Lexical err) = "Lexing: " ++ show err
  show (Parsing err) = "Parsing: " ++ show err
  show (Resolving err) = "Resolution: " ++ show err
  show (PreludeUnavailable message) = "Bundled prelude: " ++ message

public export
data DriverError
  = FrontendFailure FrontendError
  | ErasedFailure CheckError
  | RuntimeFailure RuntimeError
  | EvaluationLimit
  | PostReductionFailure RuntimeError
  | ConsoleFailure IOPlanError

public export
Show DriverError where
  show (FrontendFailure err) = show err
  show (ErasedFailure err) = "Erased checking: " ++ show err
  show (RuntimeFailure err) = "Runtime checking: " ++ show err
  show EvaluationLimit = "Evaluation budget exhausted; no normal form reported"
  show (PostReductionFailure err) = "Post-reduction checking failed: " ++ show err
  show (ConsoleFailure err) =
    "IO preparation (run requires IO Unit; use eval for pure values): " ++ show err

frontendPoint : FrontendError -> Maybe Diagnostic
frontendPoint (Parsing err) = Just (AtPoint err.position ("Parsing: " ++ err.message))
frontendPoint (Resolving err) =
  Just (AtPoint err.position ("Resolution: Unbound name " ++ show err.name))
frontendPoint (Lexical (UnexpectedChar position char)) =
  Just (AtPoint position ("Lexing: Unexpected character " ++ show char))
frontendPoint (Lexical (InvalidSource err)) =
  Just (AtPoint err.position ("Lexing: " ++ show err.problem ++
                             " (code point " ++ show err.codePoint ++ ")"))
frontendPoint (Lexical (BadString err)) = Just (AtPoint err.position ("Lexing: " ++ err.message))
frontendPoint (Lexical ScanLimit) = Nothing
frontendPoint (PreludeUnavailable _) = Nothing

||| Only genuine frontend source points; core failures remain unlocated.
public export
driverDiagnostic : DriverError -> Maybe Diagnostic
driverDiagnostic (FrontendFailure err) = frontendPoint err
driverDiagnostic _ = Nothing

public export
renderDriverError : String -> String -> DriverError -> String
renderDriverError path source (FrontendFailure err) =
  case frontendPoint err of
    Just diagnostic => renderDiagnostic path source diagnostic
    Nothing => renderFileError path (show err)
renderDriverError path source err = renderFileError path (show err)

||| Source syntax and resolved raw terms are not checking certificates.
public export
data SourceProgram = CoreSource (Term 0)

||| Every program uses the same parser and lexical/global resolver, including IO.
public export
prepareSource : String -> Either FrontendError SourceProgram
prepareSource source = do
  document <- case parseDocument 64 256 source of
    Left (SymbolLexical err) => Left (Lexical err)
    Left (SymbolParsing err) => Left (Parsing err)
    Right document => Right document
  case document.moduleHeader of
    Just header => Left (Parsing (ParseFailure header.span.start "Module checking is not implemented"))
    Nothing => Right ()
  case document.imports of
    first :: _ => Left (Parsing (ParseFailure first.span.start "Import checking is not implemented"))
    [] => Right ()
  syntax <- case document.body of
    ExpressionDocument expression => Right expression
    EmptyDocument => Left (Parsing (ParseFailure document.end "Expected expression"))
    DeclarationDocument declarations =>
      if any (\decl => decl.name == "main") declarations
         then Right (lowerDeclarations document.end declarations)
         else Left (Parsing (ParseFailure document.end "Declaration file requires a main definition"))
  globals <- case preludeGlobals of
    Left err => Left (PreludeUnavailable err)
    Right globals => Right globals
  case resolveClosedWith globals syntax of
    Left err => Left (Resolving err)
    Right term => Right (CoreSource term)

public export
resolveSource : String -> Either FrontendError (Term 0)
resolveSource source = do
  CoreSource term <- prepareSource source
  Right term

public export
record RuntimeSource where
  constructor PreparedRuntime
  term : Term 0
  inferredType : Term 0

public export
prepareRuntimeSourceDetailed : String -> Either DriverError RuntimeSource
prepareRuntimeSourceDetailed source = do
  term <- case resolveSource source of
    Left err => Left (FrontendFailure err)
    Right term => Right term
  case inferRuntime checkingDepth typeReductionFuel Empty term of
    Left err => Left (RuntimeFailure err)
    Right checked => Right (PreparedRuntime term checked.inferredType)

public export
prepareRuntimeSource : String -> Either String RuntimeSource
prepareRuntimeSource source = case prepareRuntimeSourceDetailed source of
  Left err => Left (show err)
  Right prepared => Right prepared

-- Display normalization is not an extra acceptance obligation.
renderType : Term 0 -> String
renderType ty = case normalize 128 ty of
  Normal normal => renderTerm normal
  OutOfFuel _ => renderTerm ty ++ " (display normalization exhausted)"

public export
checkSourceDetailed : Bool -> String -> Either DriverError (List String)
checkSourceDetailed erasedOnly source = do
  term <- case resolveSource source of
    Left err => Left (FrontendFailure err)
    Right term => Right term
  if erasedOnly
     then case inferErased checkingDepth typeReductionFuel Empty term of
       Left err => Left (ErasedFailure err)
       Right ty => Right ["Erased checking: accepted (no runtime-use guarantee)", "Type: " ++ renderType ty]
     else case inferRuntime checkingDepth typeReductionFuel Empty term of
       Left err => Left (RuntimeFailure err)
       Right checked => Right ["Runtime checking: accepted", "Type: " ++ renderType checked.inferredType]

public export
checkSource : Bool -> String -> Either String (List String)
checkSource erasedOnly source = case checkSourceDetailed erasedOnly source of
  Left err => Left (show err)
  Right lines => Right lines

public export
checkFile : Bool -> String -> IO (Either String (List String))
checkFile erasedOnly path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (renderFileError path (show err))
    Right source => case checkSourceDetailed erasedOnly source of
      Left err => Left (renderDriverError path source err)
      Right lines => Right lines
