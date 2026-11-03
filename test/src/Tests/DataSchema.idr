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
  , ("empty input yields no data layout hints", null (exportedDataSchemas "Example" []))
  ]
