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
exportedDataSchemas moduleName (MutualDataItem _ members :: rest) =
  map (DataSchemaHint moduleName) (filter exported members) ++ exportedDataSchemas moduleName rest
exportedDataSchemas moduleName (_ :: rest) = exportedDataSchemas moduleName rest

||| Syntactic branch header. The arity is the number of authored field binders;
||| it is not a field-type, quantity, exhaustiveness or typing certificate.
public export
record CaseArmHeader where
  constructor ArmHeader
  constructorName : String
  binderCount : Nat

public export
record CasePlanError where
  constructor InvalidCasePlan
  message : String

public export
Show CasePlanError where
  show err = err.message

||| Match names against one supplied declaration in constructor order. A caller
||| must reserve the supplied budget before using the result; this helper does
||| not validate scrutinee type, constructor identity/packing or branch terms.
||| The original indices make reordering explicit and avoid rewriting branches.
public export
planDataArms : Nat -> DataSchema -> List CaseArmHeader -> Either CasePlanError (List Nat)
planDataArms budget schema arms = do
  let constructors = schema.declaration.constructors
  if length constructors + length arms > budget
     then Left (InvalidCasePlan "Data-case coverage budget exhausted") else Right ()
  if null constructors then Left (InvalidCasePlan "Empty data layout") else Right ()
  let names = map (\ctor => ctor.name.spelling) constructors
  if length (nub names) /= length names then Left (InvalidCasePlan "Duplicate constructor in data layout") else Right ()
  let supplied = map constructorName arms
  if length (nub supplied) /= length supplied then Left (InvalidCasePlan "Duplicate data-case constructor") else Right ()
  if any (\name => not (elem name names)) supplied then Left (InvalidCasePlan "Unknown data-case constructor") else Right ()
  traverse (choose arms) constructors
  where
    choose : List CaseArmHeader -> DataConstructor -> Either CasePlanError Nat
    choose supplied ctor = search 0 supplied
      where
        search : Nat -> List CaseArmHeader -> Either CasePlanError Nat
        search _ [] = Left (InvalidCasePlan ("Missing data-case constructor " ++ ctor.name.spelling))
        search index (arm :: rest) =
          if arm.constructorName /= ctor.name.spelling then search (S index) rest
          else if arm.binderCount /= length ctor.fields
            then Left (InvalidCasePlan ("Wrong number of fields for " ++ ctor.name.spelling))
            else Right index

||| Select only explicitly named direct imports, never every loaded/transitive
||| module. The caller must provide the independently checked module inventory;
||| this ordinary public list is not itself an authority or certificate.
public export
selectDataImports : List String -> List (String, List DataSchema) -> Either CasePlanError (List DataSchema)
selectDataImports names modules = do
  if length (nub names) /= length names then Left (InvalidCasePlan "Duplicate data-schema import") else Right ()
  selected <- traverse select names
  Right (concat selected)
  where
    select : String -> Either CasePlanError (List DataSchema)
    select name = case filter (\(key, _) => key == name) modules of
      [(_, schemas)] => if all (\schema => schema.moduleName == name) schemas then Right schemas
                          else Left (InvalidCasePlan "Mismatched data-schema origin")
      [] => Left (InvalidCasePlan "Missing direct-import data-schema inventory")
      _ => Left (InvalidCasePlan "Ambiguous direct-import data-schema inventory")
