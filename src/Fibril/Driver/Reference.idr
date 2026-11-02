-- Bounded, explicit reference data: documentation is not a source definition.
module Fibril.Driver.Reference

import Data.List
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Document
import Fibril.Source.Declaration
import Fibril.Source.Navigation
import Fibril.Source.Primitive
import Fibril.Source.Global
import Fibril.Source.File
import Fibril.Source.Diagnostic
import Fibril.Driver.Check
import Fibril.Driver.PreludeSource
import Fibril.Driver.JSON

%default total

public export
data ReferenceTarget = BuiltinReference String (List String)
                    | PreludeReference String SourceSpan

data Meaning = Local | Standard String

builtin : String -> Maybe (List String)
builtin "String" = Just ["String : Type 0", "Built-in UTF-8 text values; literals use double quotes.",
  "Concatenation/comparison use appendString/equalString. Equality is exact text, not Unicode normalization or a dependent equality proof."]
builtin "Unit" = Just ["Unit : Type 0", "One constructor: ().", "Use case value of () => body to consume a linear Unit."]
builtin "Bool" = Just ["Bool : Type 0", "Constructors: True and False.", "Use if condition then yes else no. Branch resources obey the compiler's quantitative join rule."]
builtin "Type" = Just ["Type n : Type (n + 1)", "Universe levels are explicit natural literals.", "Literal-universe upward compatibility is supported; this is not general subtyping or a universe-polymorphism implementation."]
builtin name = map (\global => [name ++ " : " ++ renderType global.declaredType,
  "Compiler primitive, not a declaration in Prelude.fib.",
  if name == "IO" then "IO describes inert actions. Only the external run driver executes a validated IO Unit stdout plan."
                  else "Used by ordinary checked Prelude wrappers. This reference does not execute effects."])
  (find (\global => global.name == name) primitiveGlobals)

contains : Nat -> Nat -> SourceSpan -> Bool
contains line column span = line == span.start.line && column >= span.start.column && column < span.finish.column

parse : String -> Either DriverError ParsedDocument
parse source = case parseDocument 64 256 source of
  Left (SymbolLexical err) => Left (FrontendFailure (Lexical err))
  Left (SymbolParsing err) => Left (FrontendFailure (Parsing err))
  Right document => Right document

||| Syntax/lexical reference lookup, not checking an entire program. Local names
||| shadow unqualified globals; qualified names, literals and comments are not guessed.
public export
referenceAt : String -> Nat -> Nat -> Either DriverError (Maybe ReferenceTarget)
referenceAt source line column = do
  document <- parse source
  prelude <- parse preludeSource
  let declarations = case prelude.body of
        DeclarationDocument values => values
        _ => []
  let global : String -> Maybe Meaning = \name => if any (\decl => decl.name == name) declarations ||
                          any (\value => value.name == name) primitiveGlobals
                         then Just (Standard name) else Nothing
  let references = documentReferencesWithGlobals (const Local) global (const Nothing) document
  let selected = find (\reference => contains line column reference.origin) references
  let selectedName : Maybe String = case selected of
        Just reference => case reference.target of
          Standard name => Just name
          Local => Nothing
        Nothing => case find (\token => contains line column token.span) document.tokens of
          Just token => if elem token.kind [StringKeyword, UnitKeyword, BoolKeyword, TypeKeyword]
                           then Just token.spelling else Nothing
          Nothing => Nothing
  case selectedName of
    Nothing => Right Nothing
    Just name => case find (\decl => decl.name == name) declarations of
      Just decl => Right (Just (PreludeReference name decl.definitionNameSpan))
      Nothing => Right (map (BuiltinReference name) (builtin name))

public export
renderReference : Maybe ReferenceTarget -> String
renderReference target = protocolJSON [("reference", case target of
  Nothing => "null"
  Just (BuiltinReference name lines) => jsonObject
    [("kind", jsonString "builtin-documentation"), ("name", jsonString name),
     ("lines", jsonArray (map jsonString lines))]
  Just (PreludeReference name span) => jsonObject
    [("kind", jsonString "bundled-prelude-source"), ("name", jsonString name),
     ("source", jsonString preludeSource),
     ("range", jsonObject [("start", jsonPosition span.start), ("end", jsonPosition span.finish)])])]

public export
referenceFile : Nat -> Nat -> String -> IO (Either String (List String))
referenceFile line column path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (renderFileError path (show err))
    Right source => case referenceAt source line column of
      Left err => Left (renderDriverError path source err)
      Right target => Right [renderReference target]
