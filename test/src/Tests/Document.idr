module Tests.Document

import Data.List
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Declaration
import Fibril.Source.Document
import Fibril.Source.Symbol
import Fibril.Source.Rename
import Fibril.Driver.Check

%default total

fails : String -> Bool
fails source = case parseDocument 64 256 source of Left _ => True; _ => False

importsText : Nat -> String
importsText Z = ""
importsText (S n) = "import M" ++ show n ++ "\n" ++ importsText n

public export
checks : List (String, Bool)
checks =
  [ ("document retains module and import names with keyword components",
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
        Left err => isInfixOf (unpack "Module loading is not implemented") (unpack err)
        _ => False)
  , ("document import entry does not authorize dependency loading",
      case checkSource False "import A\nmain : Bool\nmain = True" of
        Left err => isInfixOf (unpack "Import loading is not implemented") (unpack err)
        _ => False)
  , ("document module rename requires project scope",
      case previewRename "module A\nvalue : Bool\nvalue = True" 2 1 "renamed" of
        Left RenameModuleUnsupported => True
        _ => False)
  ]
