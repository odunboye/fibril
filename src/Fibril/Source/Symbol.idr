-- Syntax-only document metadata, reusable with unsaved source buffers.
module Fibril.Source.Symbol

import Data.List
import public Fibril.Source.Document
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Parser
import Fibril.Source.Declaration

%default total

public export
record DocumentSymbol where
  constructor Symbol
  name : String
  quantity : Quantity
  range : SourceSpan
  selection : SourceSpan
  definitionSelection : SourceSpan
  exported : Bool

||| Compatibility alias for the now-shared document parser errors.
public export
SymbolError : Type
SymbolError = DocumentError

fromDeclaration : BindingSite -> DocumentSymbol
fromDeclaration decl = Symbol decl.name decl.quantity decl.span
                              decl.nameSpan decl.definitionNameSpan decl.exported

||| Complete syntactic declarations only; no resolution/typing or partial results.
||| Library fragments without main and empty editor buffers are supported.
public export
documentSymbols : String -> Either SymbolError (List DocumentSymbol)
documentSymbols source = do
  document <- parseDocument 64 256 source
  rejectCubicalMetadataInspection document
  case document.body of
    DeclarationDocument values => Right (map fromDeclaration (concatMap bindingSites values))
    _ => Right []
