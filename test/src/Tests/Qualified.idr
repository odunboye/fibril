module Tests.Qualified

import Data.List
import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Source.Text
import Fibril.Source.Syntax
import Fibril.Source.Document
import Fibril.Source.Global
import Fibril.Source.Resolve

%default total

identity : GlobalDefinition
identity = Global "Tools.String.identity" (Pi Linear StringType StringType)
                  (Lambda Linear StringType (Variable FZ))

resolved : List GlobalDefinition -> String -> Maybe (Term 0)
resolved globals source = case parseDocument 64 256 source of
  Right document => case document.body of
    ExpressionDocument expr => case resolveClosedWith globals expr of
      Right term => Just term
      _ => Nothing
    _ => Nothing
  _ => Nothing

parses : String -> Bool
parses source = case parseDocument 64 256 source of Right _ => True; _ => False

public export
checks : List (String, Bool)
checks =
  [ ("qualified references apply a supplied closed binding",
      case resolved [identity] "Tools.String.identity \"hello\"" of
        Just term => case (checkRuntime 256 128 Empty term StringType, normalize 128 term) of
          (Right _, Normal (StringValue value)) => value == "hello"
          _ => False
        _ => False)
  , ("qualified references are not captured by a local prefix",
      case resolved [identity] "let (1 Tools : Unit) = () in case Tools of () => Tools.String.identity \"module\"" of
        Just term => case checkRuntime 256 128 Empty term StringType of
          Right _ => True
          _ => False
        _ => False)
  , ("global lookup preserves an upward declared signature",
      case resolved [Global "Types.Bit" (Universe 1) BoolType] "Types.Bit" of
        Just term => case inferErased 256 128 Empty term of
          Right ty => sameSyntax ty (Universe 1)
          _ => False
        _ => False)
  , ("global ascription does not add conversion opacity",
      case resolved [Global "Types.Bit" (Universe 1) BoolType] "Types.Bit" of
        Just term => case normalize 128 term of Normal BoolType => True; _ => False
        _ => False)
  , ("global metadata is not a typing axiom",
      case resolved [Global "Bad.value" BoolType (StringValue "wrong")] "Bad.value" of
        Just term => case checkRuntime 256 128 Empty term BoolType of Left _ => True; _ => False
        _ => False)
  , ("erased globals are available to erased checking, not runtime values",
      case resolved [GlobalWithQuantity Erased "Hidden.bit" BoolType BoolTrue] "Hidden.bit" of
        Just term => case (checkErased 256 128 Empty term BoolType, checkRuntime 256 128 Empty term BoolType) of
          (Right (), Left _) => True
          _ => False
        _ => False)
  , ("erased global lookup still preserves the published universe",
      case resolved [GlobalWithQuantity Erased "Types.Bit" (Universe 1) BoolType] "Types.Bit" of
        Just term => case inferErased 256 128 Empty term of
          Right ty => sameSyntax ty (Universe 1)
          _ => False
        _ => False)
  , ("erased metadata does not turn an invalid body into an axiom",
      case resolved [GlobalWithQuantity Erased "Hidden.bad" BoolType (StringValue "wrong")] "Hidden.bad" of
        Just term => case checkErased 256 128 Empty term BoolType of Left _ => True; _ => False
        _ => False)
  , ("linear global metadata is not accepted as reusable ownership",
      case lookupGlobal "Hidden.linear" [GlobalWithQuantity Linear "Hidden.linear" BoolType BoolTrue] of
        Nothing => True
        _ => False)
  , ("qualified syntax accepts sixteen module components",
      parses (concat (intersperse "." (replicate 16 "A")) ++ ".value"))
  , ("qualified syntax rejects seventeen module components",
      not (parses (concat (intersperse "." (replicate 17 "A")) ++ ".value")))
  , ("qualified syntax is not value projection", not (parses "object.field"))
  , ("qualified syntax rejects lowercase intermediate components", not (parses "Tools.lower.value"))
  , ("qualified syntax requires a value identifier",
      not (parses "Tools.String") && not (parses "Tools._") && not (parses "Tools."))
  , ("qualified syntax remains on one source line", not (parses "Tools.\n  value"))
  ]
