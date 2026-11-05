module Tests.ReadLine

import Data.Fin
import Data.List
import Data.String
import Fibril.Driver.Interactive
import Fibril.Driver.Check
import Fibril.Effect.ConsoleProgram
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Renaming
import Fibril.Core.Substitution
import Fibril.Core.Substitution.Composition
import Fibril.Driver.Console
import Fibril.Driver.Native.Emit
import Fibril.Effect.Console

%default total

accepted : Term 0 -> Term 0 -> Bool
accepted term ty = case checkRuntime 512 128 Empty term ty of
  Left _ => False
  Right _ => True

consumingRead : Term 0
consumingRead = IOBind readResultType UnitType ReadLine
  (Lambda Linear readResultType
    (VariantCase (Lambda Erased readResultType (IOType UnitType)) (Variable FZ)
      [IOPure UnitValue,
       Lambda Linear StringType (WriteLine (Variable FZ)),
       Lambda Linear StringType (WriteLine (Variable FZ))]))

sourceAccepted : String -> Bool
sourceAccepted source = case checkSource False source of
  Left _ => False
  Right _ => True

scripted : List ConsoleScriptStep -> Bool
scripted script = case prepareInteractive 128 128 consumingRead of
  Left _ => False
  Right program => case runScript 2 script program of
    Scripted (Right (Right ())) [] transcript => length transcript == length script
    _ => False

public export
checks : List (String, Bool)
checks =
  [ ("source readLine has an explicit result type",
      sourceAccepted "main : IO ReadResult\nmain = readLine")
  , ("source readLine is not IO String",
      not (sourceAccepted "main : IO String\nmain = readLine"))
  , ("source read result cannot be silently discarded",
      not (sourceAccepted "main : IO Unit\nmain = bind ReadResult Unit readLine (\\(1 result : ReadResult) => pure Unit ())"))
  , ("source read case rejects duplicate line payload use",
      not (sourceAccepted "handle : (1 result : ReadResult) -> IO Unit\nhandle = \\(1 result : ReadResult) => readCase (IO Unit) result (pure Unit ()) (\\(1 text : String) => putStrLn (appendString text text)) (\\(1 message : String) => putStrLn message)\nmain : IO Unit\nmain = bind ReadResult Unit readLine handle"))
  , ("source read case rejects discarded error payload",
      not (sourceAccepted "handle : (1 result : ReadResult) -> IO Unit\nhandle = \\(1 result : ReadResult) => readCase (IO Unit) result (pure Unit ()) (\\(1 text : String) => putStrLn text) (\\(1 message : String) => pure Unit ())\nmain : IO Unit\nmain = bind ReadResult Unit readLine handle"))
  , ("interactive core line response determines following output",
      scripted [SupplyLine (Right (Just "hello")), ExpectWrite "hello" (Right ())])
  , ("interactive core EOF completes without a write",
      scripted [SupplyLine (Right Nothing)])
  , ("interactive core represented input failure reaches its error branch",
      scripted [SupplyLine (Left "input failed"), ExpectWrite "input failed" (Right ())])
  , ("interactive core write failure remains distinct from input failure",
      case prepareInteractive 128 128 consumingRead of
        Left _ => False
        Right program => case runScript 2
          [SupplyLine (Right (Just "hello")), ExpectWrite "hello" (Left "write failed")] program of
            Scripted (Right (Left (InteractiveWriteFailure "write failed"))) [] transcript =>
              length transcript == 2
            _ => False)
  , ("interactive core rejects wrong entry before exposing requests",
      case prepareInteractive 128 128 (IOPure (StringValue "not unit")) of
        Left _ => True
        Right _ => False)
  , ("interactive core request budget exhaustion retains input prefix",
      case prepareInteractive 128 128 consumingRead of
        Left _ => False
        Right program => case runScript 1
          [SupplyLine (Right (Just "hello")), ExpectWrite "hello" (Right ())] program of
            Scripted (Left ScriptFuelLimit) remaining transcript =>
              length transcript == 1 && length remaining == 1
            _ => False)
  , ("core read request has explicit result alternatives",
      accepted ReadLine (IOType readResultType))
  , ("core read request cannot be a pure String",
      not (accepted ReadLine StringType))
  , ("core read request full normalization remains inert",
      case normalize 0 (the (Term 0) ReadLine) of
        Normal ReadLine => True
        _ => False)
  , ("core read request head normalization remains inert",
      case weakHead 0 (the (Term 0) ReadLine) of
        HeadForm ReadLine => True
        _ => False)
  , ("core read request survives scope transport",
      sameSyntax (rename FS (the (Term 0) ReadLine)) (the (Term 1) ReadLine))
  , ("core read result admits EOF",
      accepted (VariantValue readResultType 0 Nothing) readResultType)
  , ("core read result admits a line",
      accepted (VariantValue readResultType 1 (Just (StringValue "line"))) readResultType)
  , ("core read result admits a represented error",
      accepted (VariantValue readResultType 2 (Just (StringValue "failed"))) readResultType)
  , ("core read result rejects malformed EOF payload",
      not (accepted (VariantValue readResultType 0 (Just (StringValue "bad"))) readResultType))
  , ("core read result can be consumed through all alternatives",
      accepted consumingRead (IOType UnitType))
  , ("interactive emitter selects the explicit incremental entry",
      case emitCheckedInteractiveC 3 32 consumingRead of
        Right code => isInfixOf "fibril_native_interactive_run(" code &&
                      isInfixOf "f_read_line(r)" code
        Left _ => False)
  , ("interactive emitter rejects excessive line admission",
      emitCheckedInteractiveC 3 8193 consumingRead == Left "Native interactive admission limit exceeded")
  , ("interactive emitter rejects excessive request admission",
      emitCheckedInteractiveC 100001 32 consumingRead == Left "Native interactive admission limit exceeded")
  , ("native output emitter continues to reject core input",
      emitCheckedC consumingRead == Left "C backend does not support this computational core construct")
  , ("output planner cannot execute well-typed core input",
      case prepareIO 128 128 consumingRead of
        Left (PlanUnsupported _) => True
        _ => False)
  ]
