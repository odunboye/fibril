-- Authored declarations and lowered named IR. Neither is a typing certificate.
module Fibril.Source.Declaration.Syntax

import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax

%default total

public export
record Declaration where
  constructor DeclarationWithRole
  dictionary : Bool
  generated : Bool
  span : SourceSpan
  nameSpan : SourceSpan
  definitionNameSpan : SourceSpan
  exported : Bool
  quantity : Quantity
  name : String
  expected : Expr
  value : Expr

public export
Declared : Bool -> SourceSpan -> SourceSpan -> SourceSpan -> Bool -> Quantity -> String -> Expr -> Expr -> Declaration
Declared = DeclarationWithRole False

public export
Defined : SourceSpan -> SourceSpan -> SourceSpan -> Bool -> Quantity -> String -> Expr -> Expr -> Declaration
Defined = Declared False

public export
record RecordField where
  constructor Field
  token : Token
  quantity : Quantity
  ty : Expr

public export
record RecordParameter where
  constructor Parameter
  span : SourceSpan
  quantity : Quantity
  name : String
  domain : Expr

public export
record RecordProjection where
  constructor Projected
  keyword : Token
  name : Token
  field : Token

public export
record RecordDeclaration where
  constructor RecordSyntax
  span : SourceSpan
  name : Token
  level : Nat
  params : List RecordParameter
  constructorKeyword : Token
  constructorName : Token
  eliminator : Maybe (Token, Token)
  fields : List RecordField
  projections : List RecordProjection
  exported : Bool

public export
data AuthoredDeclaration = Ordinary Declaration | RecordItem RecordDeclaration
                         | InterfaceItem RecordDeclaration | ImplementationItem Declaration

public export
declarationExported : AuthoredDeclaration -> Bool
declarationExported (Ordinary decl) = decl.exported
declarationExported (RecordItem sourceRecord) = sourceRecord.exported
declarationExported (InterfaceItem sourceRecord) = sourceRecord.exported
declarationExported (ImplementationItem decl) = decl.exported

public export
isRecord : AuthoredDeclaration -> Bool
isRecord (RecordItem _) = True
isRecord (InterfaceItem _) = True
isRecord _ = False

public export
requiresElaboration : AuthoredDeclaration -> Bool
requiresElaboration (Ordinary _) = False
requiresElaboration _ = True

public export
record BindingSite where
  constructor Binding
  name : String
  quantity : Quantity
  span : SourceSpan
  nameSpan : SourceSpan
  definitionNameSpan : SourceSpan
  exported : Bool

recordSites : RecordDeclaration -> List BindingSite
recordSites sourceRecord =
  [Binding sourceRecord.name.spelling Erased sourceRecord.span sourceRecord.name.span sourceRecord.name.span sourceRecord.exported,
   Binding sourceRecord.constructorName.spelling Unrestricted
     (Between sourceRecord.constructorKeyword.span.start sourceRecord.constructorName.span.finish)
     sourceRecord.constructorName.span sourceRecord.constructorName.span sourceRecord.exported] ++
  (case sourceRecord.eliminator of
    Nothing => []
    Just (keyword, name) => [Binding name.spelling Unrestricted
      (Between keyword.span.start name.span.finish) name.span name.span sourceRecord.exported]) ++
  map (\projection => Binding projection.name.spelling Unrestricted
       (Between projection.keyword.span.start projection.field.span.finish)
       projection.name.span projection.name.span sourceRecord.exported) sourceRecord.projections

||| Authored binding locations only. Does not expand expressions or admit getters.
public export
bindingSites : AuthoredDeclaration -> List BindingSite
bindingSites (Ordinary decl) =
  [Binding decl.name decl.quantity decl.span decl.nameSpan decl.definitionNameSpan decl.exported]
bindingSites (ImplementationItem decl) =
  [Binding decl.name decl.quantity decl.span decl.nameSpan decl.definitionNameSpan decl.exported]
bindingSites (InterfaceItem sourceRecord) =
  recordSites sourceRecord ++
  map (\field => Binding field.token.spelling Unrestricted
    field.token.span field.token.span field.token.span sourceRecord.exported) sourceRecord.fields
bindingSites (RecordItem sourceRecord) = recordSites sourceRecord

public export
ordinaryDeclarations : List AuthoredDeclaration -> List Declaration
ordinaryDeclarations [] = []
ordinaryDeclarations (Ordinary decl :: rest) = decl :: ordinaryDeclarations rest
ordinaryDeclarations (RecordItem _ :: rest) = ordinaryDeclarations rest
ordinaryDeclarations (InterfaceItem _ :: rest) = ordinaryDeclarations rest
ordinaryDeclarations (ImplementationItem decl :: rest) = decl :: ordinaryDeclarations rest
