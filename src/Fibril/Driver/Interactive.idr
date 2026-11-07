-- Checked incremental core interpretation into host requests; no host IO here.
module Fibril.Driver.Interactive

import Fibril.Core.Context
import Fibril.Core.Term
import Fibril.Core.EffectAdmission
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Limits
import Fibril.Effect.ConsoleProgram

%default total

public export
data InteractiveError
  = InteractiveTyping RuntimeError
  | InteractiveDepthLimit
  | InteractiveReductionLimit
  | InteractiveExpectedString
  | InteractiveExpectedUnit
  | InteractiveUnsupported
  | InteractiveWriteFailure String

public export
Show InteractiveError where
  show (InteractiveTyping err) = "Interactive check: " ++ show err
  show InteractiveDepthLimit = "Interactive description depth exhausted"
  show InteractiveReductionLimit = "Interactive reduction budget exhausted"
  show InteractiveExpectedString = "Interactive write did not normalize to String"
  show InteractiveExpectedUnit = "Interactive main did not normalize to Unit"
  show InteractiveUnsupported = "Unsupported interactive IO description"
  show (InteractiveWriteFailure err) = "Interactive write failed: " ++ err

||| Response conversion is pure; input failure is a value, not a core exception.
public export
readResponseValue : Either String (Maybe String) -> Term 0
readResponseValue (Right Nothing) = VariantValue readResultType 0 Nothing
readResponseValue (Right (Just line)) = VariantValue readResultType 1 (Just (StringValue line))
readResponseValue (Left err) = VariantValue readResultType 2 (Just (StringValue err))

validate : Term 0 -> Term 0 -> Either InteractiveError ()
validate term ty = case checkRuntime checkingDepth typeReductionFuel Empty term ty of
  Left err => Left (InteractiveTyping err)
  Right _ => Right ()

normal : Nat -> Term 0 -> Either InteractiveError (Term 0)
normal fuel term = case normalize fuel term of
  OutOfFuel _ => Left InteractiveReductionLimit
  Normal value => Right value

-- Only recursive description depth decreases here. Host request fuel is a
-- separate interpreter budget; neither is a time/allocation bound.
compile : Nat -> Nat -> Term 0 -> ConsoleProgram (Either InteractiveError (Term 0))
compile Z fuel term = Finished (Left InteractiveDepthLimit)
compile (S depth) fuel term =
  case weakHead fuel term of
    HeadLimit _ => Finished (Left InteractiveReductionLimit)
    HeadForm head => case inferRuntime checkingDepth typeReductionFuel Empty head of
      Left err => Finished (Left (InteractiveTyping err))
      Right _ => case head of
        IOPure value => Finished (Right value)
        ReadLine => Await ReadLineRequest (\response =>
          let value = readResponseValue response in
            Finished (case validate value readResultType of
              Left err => Left err
              Right () => Right value))
        WriteLine text => case normal fuel text of
          Left err => Finished (Left err)
          Right (StringValue value) => Await (WriteRequest value) (\response =>
            Finished (case response of
              Left err => Left (InteractiveWriteFailure err)
              Right () => Right UnitValue))
          Right _ => Finished (Left InteractiveExpectedString)
        IOBind a b action next =>
          thenConsole (compile depth fuel action) (\first => case first of
            Left err => Finished (Left err)
            Right value => case validate value a of
              Left err => Finished (Left err)
              Right () => thenConsole (compile depth fuel (Apply next value))
                (\following => Finished (case following of
                  Left err => Left err
                  Right result => case validate result b of
                    Left err => Left err
                    Right () => Right result)))
        _ => Finished (Left InteractiveUnsupported)

||| Check the original closed entry before exposing any requests. Unlike the
||| stdout planner, later computation is checked incrementally and can fail after
||| earlier effects. The caller supplies host request fuel and flushing policy.
public export
prepareInteractive : Nat -> Nat -> Term 0 ->
                     Either InteractiveError (ConsoleProgram (Either InteractiveError ()))
prepareInteractive depth fuel term = do
  if containsBinaryRequest term then Left InteractiveUnsupported else Right ()
  validate term (IOType UnitType)
  Right (thenConsole (compile depth fuel term) (\result => Finished (do
    value <- result
    checked <- normal fuel value
    validate checked UnitType
    case checked of
      UnitValue => Right ()
      _ => Left InteractiveExpectedUnit)))
