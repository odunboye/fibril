-- Dictionary layout metadata, not a typechecking or nominal-membership certificate.
module Fibril.Elaboration.Interface

import Fibril.Source.Declaration.Syntax
import Fibril.Source.Lexer

%default total

public export
record InterfaceSchema where
  constructor Schema
  name : String
  constructorName : String
  ||| Checked origin is retained when a public facade changes the visible name.
  constructorOrigin : String
  constructorVisible : Bool
  parameterCount : Nat
  methods : List String

public export
schemaFor : String -> RecordDeclaration -> InterfaceSchema
schemaFor qualifier authored =
  Schema (qualifier ++ authored.name.spelling) (qualifier ++ authored.constructorName.spelling)
    (qualifier ++ authored.constructorName.spelling) True (length authored.params) (map (\field => field.token.spelling) authored.fields)

public export
localSchemas : Maybe String -> RecordDeclaration -> List InterfaceSchema
localSchemas Nothing authored = [schemaFor "" authored]
localSchemas (Just moduleName) authored = [schemaFor "" authored, schemaFor (moduleName ++ ".") authored]

||| Called by the driver only after all declarations in the module checked.
public export
exportedSchemas : String -> List AuthoredDeclaration -> List InterfaceSchema
exportedSchemas moduleName [] = []
exportedSchemas moduleName (InterfaceItem authored :: rest) =
  (if authored.exported then [schemaFor (moduleName ++ ".") authored] else []) ++ exportedSchemas moduleName rest
exportedSchemas moduleName (_ :: rest) = exportedSchemas moduleName rest
