-- Pure planning: resolve/check/reduce all print arguments before host execution.
module Fibril.Driver.Console

import Data.List
import Fibril.Core.Context
import Fibril.Core.Term
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Effect.Console
import Fibril.Source.Syntax
import Fibril.Source.Lexer
import Fibril.Source.Text
import Fibril.Source.Resolve
import Fibril.Source.Console

%default total

public export
data ArgumentFailure
  = ArgumentResolution ResolveError
  | ArgumentTyping RuntimeError
  | ArgumentReductionLimit
  | ArgumentRecheck RuntimeError
  | ArgumentNotLiteral

public export
Show ArgumentFailure where
  show (ArgumentResolution err) = "Resolution: " ++ show err
  show (ArgumentTyping err) = "String checking: " ++ show err
  show ArgumentReductionLimit = "Console argument normalization budget exhausted"
  show (ArgumentRecheck err) = "Post-reduction String checking failed: " ++ show err
  show ArgumentNotLiteral = "Console argument did not normalize to a String literal"

||| Argument-root provenance is not an exact source map for a core subterm error.
public export
record ConsoleArgumentError where
  constructor InArgument
  span : SourceSpan
  cause : ArgumentFailure

public export
Show ConsoleArgumentError where
  show err = "Console argument at " ++ show err.span.start ++ ": " ++ show err.cause

prepareArgument : Nat -> Expr -> Either ConsoleArgumentError ConsoleAction
prepareArgument fuel expression = do
  let span = extent expression
  term <- case resolveClosed expression of
    Left err => Left (InArgument span (ArgumentResolution err))
    Right term => Right term
  _ <- case checkRuntime 256 128 Empty term StringType of
    Left err => Left (InArgument span (ArgumentTyping err))
    Right checked => Right checked
  result <- case normalize fuel term of
    OutOfFuel _ => Left (InArgument span ArgumentReductionLimit)
    Normal result => Right result
  _ <- case checkRuntime 256 128 Empty result StringType of
    Left err => Left (InArgument span (ArgumentRecheck err))
    Right checked => Right checked
  case result of
    StringValue value => Right (PrintLine value)
    _ => Left (InArgument span ArgumentNotLiteral)

||| Pure all-or-error planning; never execute a successfully prepared prefix.
||| Fuel bounds each argument's normalization, not total work or checking.
public export
prepareConsole : Nat -> ConsoleEntry -> Either ConsoleArgumentError (List ConsoleAction)
prepareConsole fuel entry = traverse (prepareArgument fuel) entry.arguments
