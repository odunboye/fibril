module Tests.IO

import Data.List
import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Effect.Console
import Fibril.Source.Global
import Fibril.Source.Primitive
import Fibril.Driver.Check
import Fibril.Driver.Console
import Fibril.Driver.Prelude

%default total

accepted : Bool -> String -> Bool
accepted erased source = case checkSource erased source of
  Right _ => True
  Left _ => False

planned : String -> Maybe (List String)
planned source = case resolveSource source of
  Left _ => Nothing
  Right term => case prepareIO 128 128 term of
    Left _ => Nothing
    Right actions => Just (map (\(PrintLine value) => value) actions)

primitiveValid : GlobalDefinition -> Bool
primitiveValid entry =
  case checkErased 256 128 Empty entry.value entry.declaredType of
    Left _ => False
    Right () => if entry.name == "IO" then True else
      case checkRuntime 256 128 Empty entry.value entry.declaredType of
        Left _ => False
        Right _ => True

public export
checks : List (String, Bool)
checks =
  [ ("IO primitives match their declared types", all primitiveValid primitiveGlobals)
  , ("IO prelude is parsed and checked",
      case preludeGlobals of Right _ => True; Left _ => False)
  , ("putStrLn is absent from primitive name table",
      case lookupGlobal "putStrLn" primitiveGlobals of Nothing => True; _ => False)
  , ("putStrLn is an ordinary checked global",
      case preludeGlobals of
        Right globals => case lookupGlobal "putStrLn" globals of
          Just (Lambda Linear StringType _) => True
          _ => False
        Left _ => False)
  , ("IO type preserves level zero",
      case inferErased 30 30 Empty (IOType StringType) of
        Right ty => sameSyntax ty (Universe 0)
        Left _ => False)
  , ("IO type does not collapse higher universes",
      case inferErased 30 30 Empty (IOType (Universe 0)) of
        Right ty => sameSyntax ty (Universe 1)
        Left _ => False)
  , ("source IO interface only accepts small types", not (accepted True "IO (Type 0)"))
  , ("IO description is not its result proof",
      not (accepted True "main : Unit\nmain = putStrLn \"not a Unit proof\""))
  , ("IO type is not a runtime value", not (accepted False "IO Unit"))
  , ("IO primitive is inert in reference normalization",
      case normalize 0 (WriteLine (StringValue {n = 0} "not printed")) of
        Normal (WriteLine (StringValue value)) => value == "not printed"
        _ => False)
  , ("IO pure bind computes without effects",
      case normalize 2 (IOBind StringType StringType (IOPure (StringValue {n = 0} "x"))
                        (Lambda Linear StringType (IOPure (Variable FZ)))) of
        Normal (IOPure (StringValue value)) => value == "x"
        _ => False)
  , ("IO pure Unit produces no host requests",
      planned "main : IO Unit\nmain = pure Unit ()" == Just [])
  , ("IO bind passes a typed result to a library function",
      planned "main : IO Unit\nmain = bind String Unit (pure String \"bound\") (\\(1 text : String) => putStrLn text)" == Just ["bound"])
  , ("IO helpers are ordinary declarations",
      planned "say : (1 x : String) -> IO Unit\nsay = \\(1 x : String) => putStrLn x\nmain : IO Unit\nmain = say \"helper\"" == Just ["helper"])
  , ("IO linear result cannot be discarded",
      not (accepted False "main : IO Unit\nmain = bind String Unit (pure String \"linear\") (\\(1 x : String) => pure Unit ())"))
  , ("IO bind continuation quantity invariant",
      not (accepted False "main : IO Unit\nmain = bind String Unit (pure String \"value\") (\\(x : String) => putStrLn x)"))
  , ("IO erased use does not grant run permission",
      accepted True "main : IO Unit\nmain = (\\(0 x : String) => putStrLn x) \"erased\"" &&
      not (accepted False "main : IO Unit\nmain = (\\(0 x : String) => putStrLn x) \"erased\""))
  , ("IO plan rejects wrong main type",
      case prepareIO 128 128 (IOPure (StringValue "not Unit")) of
        Left (PlanTyping _) => True
        _ => False)
  , ("IO plan has an explicit depth limit",
      case prepareIO 0 128 (IOPure UnitValue) of
        Left PlanDepthLimit => True
        _ => False)
  ]
