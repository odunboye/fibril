module Tests.ConsoleArguments

import Data.List
import Fibril.Core.Term
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Effect.Console
import Fibril.Source.Console
import Fibril.Driver.Console
import Fibril.Driver.Check
import Fibril.Driver.Evaluate

%default total

entryHeader : String
entryHeader = "main : IO Unit\nmain = putStrLn "

accepted : String -> Bool
accepted expression = case checkSource False (entryHeader ++ expression) of
  Right _ => True
  Left _ => False

planned : Nat -> String -> Maybe (List String)
planned fuel expression = case prepareSource (entryHeader ++ expression) of
  Right (ConsoleSource entry) => case prepareConsole fuel entry of
    Right actions => Just (map (\(PrintLine value) => value) actions)
    Left _ => Nothing
  _ => Nothing

public export
checks : List (String, Bool)
checks =
  [ ("console pure linear identity prints its result",
      planned 1 "((\\(1 text : String) => text) \"hello\")" == Just ["hello"])
  , ("console pure conditional selects string",
      planned 1 "(if False then \"first\" else \"second\")" == Just ["second"])
  , ("console pure let preserves lexical scope",
      planned 1 "(let (1 message : String) = \"local\" in message)" == Just ["local"])
  , ("console pure polymorphic function",
      planned 2 "((\\(0 A : Type 0) => \\(1 x : A) => x) String \"poly\")" == Just ["poly"])
  , ("console arguments require String",
      case checkSourceDetailed False (entryHeader ++ "True") of
        Left (ConsoleFailure err) => case err.cause of
          ArgumentTyping (TypingError (TypeMismatch actual expected)) =>
            sameSyntax actual BoolType && sameSyntax expected StringType
          _ => False
        _ => False)
  , ("console unknown reference retains structured resolution",
      case checkSourceDetailed False (entryHeader ++ "missing") of
        Left (ConsoleFailure err) => case err.cause of
          ArgumentResolution _ => True
          _ => False
        _ => False)
  , ("console cannot normalize away invalid linear discard",
      not (accepted "((\\(1 x : String) => \"constant\") \"input\")"))
  , ("console cannot normalize away erased extraction",
      not (accepted "((\\(0 x : String) => x) \"input\")"))
  , ("console checks an erased argument before beta can discard it",
      not (accepted "((\\(0 x : String) => \"constant\") True)"))
  , ("console validates both branches before selecting one",
      not (accepted "(if True then \"selected\" else False)"))
  , ("console core type data rejected", not (accepted "String"))
  , ("console function-valued argument rejected", not (accepted "(\\(1 x : String) => x)"))
  , ("console normal literal accepts zero reduction budget",
      planned 0 "\"zero\"" == Just ["zero"])
  , ("console argument budget exhaustion stays structured",
      case prepareSource (entryHeader ++ "(\"one\" : String)") of
        Right (ConsoleSource entry) => case prepareConsole 0 entry of
          Left err => case err.cause of
            ArgumentReductionLimit => True
            _ => False
          Right _ => False
        _ => False)
  , ("console later argument failure yields no prepared prefix",
      case prepareSource "main : IO Unit\nmain = do\n  putStrLn \"first\"\n  putStrLn True" of
        Right (ConsoleSource entry) => case prepareConsole 128 entry of
          Left _ => True
          Right _ => False
        _ => False)
  , ("console late normalization exhaustion yields no prepared prefix",
      case prepareSource "main : IO Unit\nmain = do\n  putStrLn \"first\"\n  putStrLn (\"second\" : String)" of
        Right (ConsoleSource entry) => case prepareConsole 0 entry of
          Left err => case err.cause of
            ArgumentReductionLimit => True
            _ => False
          Right _ => False
        _ => False)
  , ("console expressions still excluded from ordinary evaluation",
      case evaluateSourceDetailed 128 (entryHeader ++ "\"text\"") of
        Left EffectfulEvaluation => True
        _ => False)
  ]
