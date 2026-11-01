module Tests.Rename

import Data.List
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Rename

%default total

public export
checks : List (String, Bool)
checks =
  [ ("rename previews include binder and use",
      case previewRename "\\(1 x : Bool) => x" 1 18 "flag" of
        Right preview => preview.replacement == "flag" && length preview.edits == 2
        Left _ => False)
  , ("rename same-name preview is empty",
      case previewRename "\\(1 x : Bool) => x" 1 18 "x" of
        Right preview => null preview.edits
        Left _ => False)
  , ("rename rejects capture of an outer use",
      case previewRename "let (x : Bool) = True in let (y : Bool) = False in x" 1 6 "y" of
        Left RenameChangesScope => True
        _ => False)
  , ("rename rejects newly captured unresolved uses",
      case previewRename "\\(1 x : Bool) => unknown x" 1 5 "unknown" of
        Left RenameChangesScope => True
        _ => False)
  , ("rename rejects wildcard names",
      case previewRename "\\(1 x : Bool) => x" 1 5 "_" of
        Left InvalidRenameName => True
        _ => False)
  , ("rename rejects keyword names",
      case previewRename "\\(1 x : Bool) => x" 1 5 "Bool" of
        Left InvalidRenameName => True
        _ => False)
  , ("rename rejects top-level main",
      case previewRename "main : Bool\nmain = True" 1 1 "entry" of
        Left RenameEntrypoint => True
        _ => False)
  , ("rename does not treat wildcard declaration headers as bindings",
      case previewRename "_ : Bool\n_ = True" 1 1 "value" of
        Left NoRenameTarget => True
        _ => False)
  , ("rename unresolved target is explicit",
      case previewRename "missing" 1 1 "value" of
        Left NoRenameTarget => True
        _ => False)
  ]
