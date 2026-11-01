-- Syntax-only document metadata, reusable with unsaved source buffers.
module Fibril.Source.Symbol

import Data.List
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

public export
data SymbolError = SymbolLexical LexError | SymbolParsing ParseError

fromDeclaration : Declaration -> DocumentSymbol
fromDeclaration decl = Symbol decl.name decl.quantity decl.span
                              decl.nameSpan decl.definitionNameSpan

||| Complete syntactic declarations only; no resolution/typing or partial results.
||| Library fragments without main and empty editor buffers are supported.
public export
documentSymbols : String -> Either SymbolError (List DocumentSymbol)
documentSymbols source = do
  tokens <- case lexSource source of
    Left err => Left (SymbolLexical err)
    Right tokens => Right tokens
  let end = advancePosition (At 0 1 1) (unpack source)
  case tokens of
    [] => Right []
    _ => if declarationAhead tokens
      then case parseDeclarations 64 256 end tokens of
        Left err => Left (SymbolParsing err)
        Right declarations => Right (map fromDeclaration declarations)
      else case parseExpression 256 end tokens of
        Left err => Left (SymbolParsing err)
        Right _ => Right []
