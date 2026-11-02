module Tests.Document

import Data.List
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Declaration
import Fibril.Source.Document
import Fibril.Source.Symbol
import Fibril.Source.Rename
import Fibril.Driver.Check
import Fibril.Elaboration.Declaration

%default total

fails : String -> Bool
fails source = case parseDocument 64 256 source of Left _ => True; _ => False

elaborationFails : String -> Bool
elaborationFails source = case parseDocument 64 256 source of
  Left _ => True
  Right document => case document.body of
    DeclarationDocument authored => case elaborateDeclarations 64 authored of Left _ => True; _ => False
    _ => False

importsText : Nat -> String
importsText Z = ""
importsText (S n) = "import M" ++ show n ++ "\n" ++ importsText n

recordSource : String
recordSource = "module Library\nexport\nrecord Package : Type 1 where\n  constructor MkPackage\n  eliminator unpackPackage\n  0 Item : Type 0\n  1 value : Item\n"

parameterRecord : Nat -> String
parameterRecord count = "module Test\nrecord R " ++
  concat (map (\i => "(0 A" ++ show i ++ " : Type 0) ") [0 .. count]) ++
  ": Type 0 where\n  constructor MkR\n  eliminator useR\n  1 x : Bool\n  1 y : Bool\n"

public export
checks : List (String, Bool)
checks =
  [ ("parsing retains an authored record, not expanded functions",
      case parseDocument 64 256 recordSource of
        Right document => case document.body of
          DeclarationDocument [RecordItem sourceRecord] =>
            sourceRecord.name.spelling == "Package" &&
            sourceRecord.first.token.spelling == "Item" && sourceRecord.second.token.spelling == "value"
          _ => False
        _ => False)
  , ("requested projections retain actual name selections",
      case documentSymbols "module A\nexport\nrecord R : Type 0 where\n  constructor MkR\n  eliminator useR\n  x : Bool\n  y : Bool\n  projection getX x\n" of
        Right [ty, ctor, elim, getter] => getter.name == "getX" && getter.exported &&
          getter.definitionSelection.start.line == 8 && getter.quantity == Unrestricted
        _ => False)
  , ("projection declarations consume an additional slot",
      case parseDocument 3 256 "module A\nrecord R : Type 0 where\n  constructor MkR\n  eliminator useR\n  x : Bool\n  y : Bool\n  projection getX x\n" of
        Left _ => True
        _ => False)
  , ("record parameter telescope accepts eight parameters", not (fails (parameterRecord 7)))
  , ("record parameter telescope rejects nine parameters", fails (parameterRecord 8))
  , ("record parameters require erased quantities",
      elaborationFails "module A\nrecord R (A : Type 0) : Type 0 where\n  constructor MkR\n  eliminator useR\n  1 x : A\n  1 y : A\n")
  , ("record parameters cannot repeat",
      elaborationFails "module A\nrecord R (0 A : Type 0) (0 A : Type 0) : Type 0 where\n  constructor MkR\n  eliminator useR\n  1 x : A\n  1 y : A\n")
  , ("record fields cannot shadow parameters",
      elaborationFails "module A\nrecord R (0 A : Type 0) : Type 0 where\n  constructor MkR\n  eliminator useR\n  1 x : A\n  1 A : A\n")
  , ("record expansion has three real, exported name selections",
      case documentSymbols recordSource of
        Right [ty, ctor, elim] => ty.name == "Package" && ctor.name == "MkPackage" &&
          elim.name == "unpackPackage" && all exported [ty, ctor, elim] &&
          ty.selection.start.line == 3 && ctor.definitionSelection.start.line == 4 &&
          elim.definitionSelection.start.line == 5
        _ => False)
  , ("record expansion consumes three declaration slots",
      case (parseDocument 2 256 recordSource, parseDocument 3 256 recordSource) of
        (Left _, Right _) => True
        _ => False)
  , ("record fields cannot repeat",
      elaborationFails "module A\nrecord R : Type 0 where\n  constructor MkR\n  eliminator useR\n  1 x : Bool\n  1 x : Bool\n")
  , ("records require a named module",
      fails "record R : Type 0 where\n  constructor MkR\n  eliminator useR\n  1 x : Bool\n  1 y : Bool\n")
  , ("document retains module and import names with keyword components",
      case parseDocument 64 256 "module Text.Greeting\nimport Data.String\n" of
        Right document => case (document.moduleHeader, document.imports) of
          (Just header, [dependency]) =>
            header.components == ["Text", "Greeting"] &&
            header.nameSpan.start.column == 8 &&
            dependency.components == ["Data", "String"] &&
            dependency.nameSpan.start.line == 2
          _ => False
        _ => False)
  , ("document retains export marker and real name selections",
      case documentSymbols "module Library\nexport\nvalue : Bool\nvalue = True" of
        Right [symbol] => symbol.exported && symbol.range.start.line == 2 &&
          symbol.selection.start.line == 3 && symbol.definitionSelection.start.line == 4
        _ => False)
  , ("document named declarations are private by default",
      case documentSymbols "module Library\nvalue : Bool\nvalue = True" of
        Right [symbol] => not symbol.exported
        _ => False)
  , ("document accepts sixteen module components",
      not (fails ("module " ++ concat (intersperse "." (replicate 16 "A")))))
  , ("document rejects seventeen module components",
      fails ("module " ++ concat (intersperse "." (replicate 17 "A"))))
  , ("document accepts thirty-two import headers",
      not (fails ("module A\n" ++ importsText 32)))
  , ("document rejects thirty-three import headers",
      fails ("module A\n" ++ importsText 33))
  , ("document rejects lowercase module components", fails "module lower.Name")
  , ("document rejects multiline headers", fails "module A.\n  B")
  , ("document rejects trailing header tokens", fails "module A extra")
  , ("document rejects duplicate imports", fails "module A\nimport B\nimport B")
  , ("document rejects late module headers", fails "import B\nmodule A")
  , ("document rejects module expressions", fails "module A\nTrue")
  , ("document export requires a module", fails "export\nmain : Bool\nmain = True")
  , ("document export must have its own line", fails "module A\nexport value : Bool\nvalue = True")
  , ("document parser does not authorize module execution",
      case checkSource False "module A\nmain : Bool\nmain = True" of
        Left err => isInfixOf (unpack "Module checking requires --source-dir") (unpack err)
        _ => False)
  , ("document import entry does not authorize dependency loading",
      case checkSource False "import A\nmain : Bool\nmain = True" of
        Left err => isInfixOf (unpack "Import checking requires --source-dir") (unpack err)
        _ => False)
  , ("document module rename requires project scope",
      case previewRename "module A\nvalue : Bool\nvalue = True" 2 1 "renamed" of
        Left RenameModuleUnsupported => True
        _ => False)
  ]
