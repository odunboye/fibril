module Tests.ConsoleArguments

import Data.List
import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Effect.Console
import Fibril.Driver.Console
import Fibril.Driver.Check

%default total

entryHeader : String
entryHeader = "main : IO Unit\nmain = putStrLn "

planned : String -> Maybe (List String)
planned expression = case resolveSource (entryHeader ++ expression) of
  Left _ => Nothing
  Right term => case prepareIO 128 128 term of
    Left _ => Nothing
    Right actions => Just (map (\(PrintLine value) => value) actions)

accepted : String -> Bool
accepted expression = case checkSource False (entryHeader ++ expression) of
  Left _ => False
  Right _ => True

public export
checks : List (String, Bool)
checks =
  [ ("IO ordinary argument identity",
      planned "((\\(1 text : String) => text) \"hello\")" == Just ["hello"])
  , ("IO ordinary conditional argument",
      planned "(if False then \"first\" else \"second\")" == Just ["second"])
  , ("IO ordinary let argument",
      planned "(let (1 message : String) = \"local\" in message)" == Just ["local"])
  , ("IO ordinary polymorphic argument",
      planned "((\\(0 A : Type 0) => \\(1 x : A) => x) String \"poly\")" == Just ["poly"])
  , ("IO ordinary type mismatch", not (accepted "True"))
  , ("IO ordinary unknown reference", not (accepted "missing"))
  , ("IO precheck rejects linear discard",
      not (accepted "((\\(1 x : String) => \"constant\") \"input\")"))
  , ("IO precheck rejects erased extraction",
      not (accepted "((\\(0 x : String) => x) \"input\")"))
  , ("IO precheck validates erased argument types",
      not (accepted "((\\(0 x : String) => \"constant\") True)"))
  , ("IO checks unselected branches", not (accepted "(if True then \"ok\" else False)"))
  , ("IO planning reduction exhaustion is explicit",
      case prepareIO 128 0 (WriteLine (Apply (Lambda Linear StringType (Variable FZ)) (StringValue "one"))) of
        Left PlanReductionLimit => True
        _ => False)
  , ("IO literal primitive needs no reduction budget",
      case prepareIO 128 0 (WriteLine (StringValue "zero")) of
        Right [PrintLine "zero"] => True
        _ => False)
  ]
