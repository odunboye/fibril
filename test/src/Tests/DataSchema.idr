-- Syntax metadata projection tests: not evidence of checked-case semantics.
module Tests.DataSchema

import Data.List
import Fibril.Core.Quantity
import Fibril.Source.Document
import Fibril.Source.Declaration.Syntax
import Fibril.Source.Lexer
import Fibril.Elaboration.DataSchema

%default total

source : String
source = "module Example\n\nexport\ndata Choice (0 A : Type 0) : Type 0 where\n  None : Choice A\n  Some : (1 item : A) -> Choice A\n\ndata Hidden : Type 0 where\n  Secret : Hidden\n"

hints : List DataSchema
hints = case parseDocument 64 256 source of
  Right document => case document.body of
    DeclarationDocument authored => exportedDataSchemas "Example" authored
    _ => []
  _ => []

public export
checks : List (String, Bool)
checks =
  [ ("data hints contain only exported authored data and qualified family identity",
      case hints of [hint] => dataName hint == "Example.Choice"; _ => False)
  , ("data hints retain source constructor order and payload quantities",
      case hints of
        [hint] => case hint.declaration.constructors of
          [none, some] => none.name.spelling == "None" && null none.fields &&
            some.name.spelling == "Some" && case some.fields of
              [field] => field.quantity == Linear && field.token.spelling == "item"
              _ => False
          _ => False
        _ => False)
  , ("coverage planning orders alternatives by declared constructor tag",
      case hints of
        [hint] => case planDataArms 4 hint [ArmHeader "Some" 1, ArmHeader "None" 0] of
          Right [1, 0] => True
          _ => False
        _ => False)
  , ("coverage planning rejects missing, duplicate, unknown, arity and admission failures",
      case hints of
        [hint] => all (\arms => case planDataArms 4 hint arms of Left _ => True; _ => False)
          [[ArmHeader "None" 0], [ArmHeader "None" 0, ArmHeader "None" 0],
           [ArmHeader "None" 0, ArmHeader "Foreign" 1], [ArmHeader "None" 0, ArmHeader "Some" 0]] &&
          (case planDataArms 3 hint [ArmHeader "None" 0, ArmHeader "Some" 1] of Left _ => True; _ => False)
        _ => False)
  , ("direct import selection does not search unimported or transitive modules",
      case hints of
        [hint] => (case selectDataImports [] [("Example", [hint])] of Right [] => True; _ => False) &&
          (case selectDataImports ["Other"] [("Example", [hint])] of Left _ => True; _ => False) &&
          (case selectDataImports ["Example"] [("Example", [hint]), ("Transitive", [hint])] of Right [_] => True; _ => False) &&
          (case selectDataImports ["Example"] [("Example", [hint]), ("Example", [hint])] of Left _ => True; _ => False) &&
          (case selectDataImports ["Example"] [("Example", [{ moduleName := "Foreign" } hint])] of Left _ => True; _ => False)
        _ => False)
  , ("empty input yields no data layout hints", null (exportedDataSchemas "Example" []))
  ]
