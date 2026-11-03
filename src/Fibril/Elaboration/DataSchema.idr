-- Authored data layout hints, not typing certificates or source-case semantics.
module Fibril.Elaboration.DataSchema

import Data.List
import Fibril.Source.Declaration.Syntax
import Fibril.Source.Lexer

%default total

||| Authored declaration retained with its true module identity. Constructor
||| order, field quantities/types and source spans remain in declaration.
||| This public value is ordinary untrusted data: consumers must validate any
||| generated terms against actual checked definitions and the core checker.
public export
record DataSchema where
  constructor DataSchemaHint
  moduleName : String
  declaration : DataDeclaration

public export
dataName : DataSchema -> String
dataName schema = schema.moduleName ++ "." ++ schema.declaration.name.spelling

||| Pure projection only; callers may supply unchecked declarations. The module
||| driver publishes this projection only after compiling every declaration.
public export
exportedDataSchemas : String -> List AuthoredDeclaration -> List DataSchema
exportedDataSchemas moduleName [] = []
exportedDataSchemas moduleName (DataItem authored :: rest) =
  (if authored.exported then [DataSchemaHint moduleName authored] else []) ++
    exportedDataSchemas moduleName rest
exportedDataSchemas moduleName (_ :: rest) = exportedDataSchemas moduleName rest
