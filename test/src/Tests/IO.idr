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
import Fibril.Source.Lexer
import Fibril.Source.Text
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
    Right () => if entry.name == "IO" || entry.quantity == Erased then True else
      case checkRuntime 256 128 Empty entry.value entry.declaredType of
        Left _ => False
        Right _ => True

public export
checks : List (String, Bool)
checks =
  map (\entry => ("primitive " ++ entry.name ++ " matches its declared type", primitiveValid entry)) primitiveGlobals ++
  [ ("IO binding arrow has its own located token",
      case lexSource "<- ->" of
        Right [binding, function] => binding.kind == BindArrow && function.kind == Arrow &&
          binding.span.start.offset == 0 && binding.span.finish.offset == 2 &&
          function.span.start.offset == 3
        _ => False)
  , ("IO primitives match their declared types", all primitiveValid primitiveGlobals)
  , ("IO prelude is parsed and checked",
      case preludeGlobals of Right _ => True; Left _ => False)
  , ("putStrLn is absent from primitive name table",
      case lookupGlobal "putStrLn" primitiveGlobals of Nothing => True; _ => False)
  , ("putStrLn is an ordinary checked global",
      case preludeGlobals of
        Right globals => case lookupGlobal "putStrLn" globals of
          Just term => case normalize 128 term of
            Normal (Lambda Linear StringType _) => True
            _ => False
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
  , ("IO map is not a primitive",
      case lookupGlobal "map" primitiveGlobals of Nothing => True; _ => False)
  , ("IO map transforms a returned value",
      planned "main : IO Unit\nmain = bind Bool Unit (map Unit Bool (\\(1 done : Unit) => case done of () => True) (pure Unit ())) (\\(1 ok : Bool) => if ok then putStrLn \"mapped\" else putStrLn \"wrong\")" == Just ["mapped"])
  , ("IO map identity preserves a String result",
      planned "main : IO Unit\nmain = bind String Unit (map String String (\\(1 text : String) => text) (pure String \"identity\")) putStrLn" == Just ["identity"])
  , ("IO map composes ordinary pure helpers",
      planned "flip : (1 flag : Bool) -> Bool\nflip = \\(1 flag : Bool) => if flag then False else True\nmain : IO Unit\nmain = bind Bool Unit (map Bool Bool flip (map Bool Bool flip (pure Bool True))) (\\(1 flag : Bool) => if flag then putStrLn \"original\" else putStrLn \"wrong\")" == Just ["original"])
  , ("IO map preserves prior output order",
      planned "main : IO Unit\nmain = bind Bool Unit (map Unit Bool (\\(1 done : Unit) => case done of () => True) (putStrLn \"first\")) (\\(1 ok : Bool) => if ok then putStrLn \"second\" else putStrLn \"wrong\")" == Just ["first", "second"])
  , ("IO map can move a captured linear value",
      accepted False "main : (1 text : String) -> IO String\nmain = \\(1 text : String) => map Unit String (\\(1 done : Unit) => case done of () => text) (pure Unit ())")
  , ("IO map rejects discarded linear results",
      not (accepted False "map String String (\\(1 text : String) => \"discard\") (pure String \"input\")"))
  , ("IO map rejects duplicated linear results before reduction",
      not (accepted False "map Bool Bool (\\(1 flag : Bool) => if flag then flag else flag) (pure Bool True)"))
  , ("IO map requires a linear function argument type",
      not (accepted False "map String String (\\(text : String) => text) (pure String \"input\")"))
  , ("IO map does not implicitly flatten returned descriptions",
      accepted False "map String (IO Unit) putStrLn (pure String \"nested\")" &&
      not (accepted False "main : IO Unit\nmain = map String (IO Unit) putStrLn (pure String \"nested\")"))
  , ("IO map returned descriptions need explicit bind",
      planned "main : IO Unit\nmain = bind (IO Unit) Unit (map String (IO Unit) putStrLn (pure String \"nested\")) (\\(1 action : IO Unit) => action)" == Just ["nested"])
  , ("IO do names a returned String",
      planned "main : IO Unit\nmain = do\n  (1 text : String) <- pure String \"named\"\n  putStrLn text" == Just ["named"])
  , ("IO do binding can feed a later binding",
      planned "main : IO Unit\nmain = do\n  (1 flag : Bool) <- pure Bool True\n  (1 text : String) <- pure String (if flag then \"yes\" else \"no\")\n  putStrLn text" == Just ["yes"])
  , ("IO do binding shadows only in subsequent statements",
      planned "text : String\ntext = \"outer\"\nmain : IO Unit\nmain = do\n  (1 text : String) <- pure String text\n  putStrLn text" == Just ["outer"])
  , ("IO do same-name binding uses the previous value on its RHS",
      planned "main : IO Unit\nmain = do\n  (1 value : Bool) <- pure Bool True\n  (1 value : String) <- pure String (if value then \"shadowed\" else \"no\")\n  putStrLn value" == Just ["shadowed"])
  , ("IO do binding annotations do not see the new name",
      not (accepted False "main : IO Unit\nmain = do\n  (1 value : value) <- pure String \"bad\"\n  putStrLn value"))
  , ("IO do binding RHS does not see the new name",
      not (accepted False "main : IO Unit\nmain = do\n  (1 value : String) <- pure String value\n  putStrLn value"))
  , ("IO do binding cannot see forward references",
      not (accepted False "main : IO Unit\nmain = do\n  putStrLn later\n  (1 later : String) <- pure String \"late\"\n  putStrLn later"))
  , ("IO do requires explicit linear bindings",
      not (accepted False "main : IO Unit\nmain = do\n  (text : String) <- pure String \"bad\"\n  putStrLn text") &&
      not (accepted False "main : IO Unit\nmain = do\n  (0 text : String) <- pure String \"bad\"\n  putStrLn text"))
  , ("IO do rejects missing continuation",
      not (accepted False "main : IO Unit\nmain = do\n  (1 text : String) <- pure String \"last\""))
  , ("IO do rejects discarded named results",
      not (accepted False "main : IO Unit\nmain = do\n  (1 text : String) <- pure String \"unused\"\n  pure Unit ()"))
  , ("IO do rejects duplicated named results",
      not (accepted False "main : IO Unit\nmain = do\n  (1 text : String) <- pure String \"twice\"\n  putStrLn text\n  putStrLn text"))
  , ("IO do validates the annotated action result",
      not (accepted False "main : IO Unit\nmain = do\n  (1 text : String) <- pure Bool True\n  putStrLn text"))
  , ("IO unannotated bound blocks return Unit",
      not (accepted False "main : IO Bool\nmain = do\n  (1 flag : Bool) <- pure Bool True\n  pure Bool flag"))
  , ("IO do Unit bindings need explicit consumption",
      planned "main : IO Unit\nmain = do\n  (1 done : Unit) <- putStrLn \"first\"\n  case done of () => putStrLn \"second\"" == Just ["first", "second"])
  , ("IO do let feeds a subsequent result binding",
      planned "main : IO Unit\nmain = do\n  let (1 text : String) = \"local\"\n  (1 value : String) <- pure String text\n  putStrLn value" == Just ["local"])
  , ("IO do unrestricted let permits reuse",
      planned "main : IO Unit\nmain = do\n  let (text : String) = \"reused\"\n  putStrLn text\n  putStrLn text" == Just ["reused", "reused"])
  , ("IO do let RHS sees the preceding binding",
      planned "main : IO Unit\nmain = do\n  let (1 text : String) = \"outer\"\n  let (1 text : String) = text\n  putStrLn text" == Just ["outer"])
  , ("IO do let does not introduce its name into its RHS",
      not (accepted False "main : IO Unit\nmain = do\n  let (1 text : String) = text\n  putStrLn text"))
  , ("IO do let annotation cannot see its own name",
      not (accepted False "main : IO Unit\nmain = do\n  let (1 text : text) = \"bad\"\n  putStrLn text"))
  , ("IO do let validates the value type",
      not (accepted False "main : IO Unit\nmain = do\n  let (text : String) = True\n  putStrLn text"))
  , ("IO do let rejects linear discard",
      not (accepted False "main : IO Unit\nmain = do\n  let (1 text : String) = \"unused\"\n  pure Unit ()"))
  , ("IO do let rejects linear duplication",
      not (accepted False "main : IO Unit\nmain = do\n  let (1 text : String) = \"twice\"\n  putStrLn text\n  putStrLn text"))
  , ("IO do let rejects erased extraction",
      not (accepted False "main : IO Unit\nmain = do\n  let (0 text : String) = \"erased\"\n  putStrLn text"))
  , ("IO do erased unused description does not execute",
      planned "main : IO Unit\nmain = do\n  let (0 ignored : IO Unit) = putStrLn \"never\"\n  pure Unit ()" == Just [])
  , ("IO do let needs a final action",
      not (accepted False "main : IO Unit\nmain = do\n  let (text : String) = \"last\""))
  , ("IO do complete let-in action remains supported",
      planned "main : IO Unit\nmain = do\n  let (1 text : String) = \"complete\" in putStrLn text\n  putStrLn \"next\"" == Just ["complete", "next"])
  , ("IO annotated do returns a bound String",
      planned "greeting : IO String\ngreeting = do (String)\n  (1 text : String) <- pure String \"returned\"\n  pure String text\nmain : IO Unit\nmain = bind String Unit greeting putStrLn" == Just ["returned"])
  , ("IO annotated do threads its result through bare actions",
      planned "greeting : IO String\ngreeting = do (String)\n  putStrLn \"first\"\n  pure String \"result\"\nmain : IO Unit\nmain = bind String Unit greeting putStrLn" == Just ["first", "result"])
  , ("IO annotated do checks a single final action",
      accepted False "main : IO Bool\nmain = do (Bool)\n  pure Bool True" &&
      not (accepted False "main : IO Bool\nmain = do (String)\n  pure Bool True"))
  , ("IO annotated do validates the result as a type",
      not (accepted False "main : IO Unit\nmain = do (True)\n  pure Unit ()"))
  , ("IO annotated do rejects a wrong continuation result",
      not (accepted False "main : IO String\nmain = do (String)\n  (1 flag : Bool) <- pure Bool True\n  pure Bool flag"))
  , ("IO annotated do retains linear result checking",
      not (accepted False "main : IO String\nmain = do (String)\n  (1 text : String) <- pure String \"unused\"\n  pure String \"discard\""))
  , ("IO annotated do preserves polymorphic scope through let and bind",
      planned "echo : (0 A : Type 0) -> (1 value : A) -> IO A\necho = \\(0 A : Type 0) => \\(1 value : A) => do (A)\n  let (1 moved : A) = value\n  (1 result : A) <- pure A moved\n  pure A result\nmain : IO Unit\nmain = bind String Unit (echo String \"polymorphic\") putStrLn" == Just ["polymorphic"])
  , ("IO do result type is not captured by a shadowing let",
      planned "keep : (0 A : Type 0) -> (1 action : IO A) -> IO A\nkeep = \\(0 A : Type 0) => \\(1 action : IO A) => do (A)\n  let (A : Bool) = True\n  action\nmain : IO Unit\nmain = bind String Unit (keep String (pure String \"outer type\")) putStrLn" == Just ["outer type"])
  , ("IO annotated do still requires a final action",
      not (accepted False "main : IO String\nmain = do (String)\n  (1 text : String) <- pure String \"last\""))
  , ("IO do annotation does not permit inline actions",
      not (accepted False "main : IO Unit\nmain = do (Unit) pure Unit ()"))
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
