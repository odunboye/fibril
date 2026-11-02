-- Inspect frontend lowering without name resolution, core checking, or effects.
module Fibril.Driver.Elaborate

import Data.List
import Fibril.Core.Quantity
import Fibril.Source.File
import Fibril.Source.Document
import Fibril.Source.Declaration
import Fibril.Source.Diagnostic
import Fibril.Source.Lexer
import Fibril.Elaboration.Declaration
import Fibril.Elaboration.Pretty
import Fibril.Driver.Check
import Fibril.Driver.JSON

%default total

declarationJSON : Declaration -> String
declarationJSON decl = jsonObject
  [("name", jsonString decl.name), ("quantity", jsonString (show decl.quantity)),
   ("implementation", if decl.dictionary then "true" else "false"),
   ("generated", if decl.generated then "true" else "false"),
   ("exported", if decl.exported then "true" else "false"),
   ("origin", jsonObject [("start", jsonPosition decl.nameSpan.start),
                          ("end", jsonPosition decl.nameSpan.finish)]),
   ("signature", jsonString (renderExpr decl.expected)),
   ("value", jsonString (renderExpr decl.value))]

||| Admission/expansion is not checking. Names/imports deliberately remain symbolic.
public export
elaborationReport : String -> Either DriverError String
elaborationReport source = do
  document <- case parseDocument 64 256 source of
    Left (SymbolLexical err) => Left (FrontendFailure (Lexical err))
    Left (SymbolParsing err) => Left (FrontendFailure (Parsing err))
    Right document => Right document
  declarations <- case document.body of
    DeclarationDocument authored => case elaborateDeclarations 64 authored of
      Left err => Left (FrontendFailure (Elaborating err))
      Right declarations => Right declarations
    _ => Right []
  Right (protocolJSON
    [("checked", "false"), ("representation", jsonString "named-ir;not-source"),
     ("module", maybe "null" (\header => jsonString (concat (intersperse "." header.components))) document.moduleHeader),
     ("imports", jsonArray (map (\dependency => jsonString (concat (intersperse "." dependency.components))) document.imports)),
     ("declarations", jsonArray (map declarationJSON declarations)),
     ("expression", case document.body of ExpressionDocument value => jsonString (renderExpr value); _ => "null")])

public export
elaborateFile : String -> IO (Either String (List String))
elaborateFile path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (renderFileError path (show err))
    Right source => case elaborationReport source of
      Left err => Left (renderDriverError path source err)
      Right report => Right [report]
