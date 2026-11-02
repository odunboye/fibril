-- Authored declarations and lowered named IR. Neither is a typing certificate.
module Fibril.Source.Declaration.Syntax

import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax

%default total

public export
record Declaration where
  constructor Declared
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
  eliminatorKeyword : Token
  eliminatorName : Token
  first : RecordField
  second : RecordField
  projections : List RecordProjection
  exported : Bool

public export
data AuthoredDeclaration = Ordinary Declaration | RecordItem RecordDeclaration

public export
declarationExported : AuthoredDeclaration -> Bool
declarationExported (Ordinary decl) = decl.exported
declarationExported (RecordItem sourceRecord) = sourceRecord.exported

public export
isRecord : AuthoredDeclaration -> Bool
isRecord (RecordItem _) = True
isRecord _ = False

public export
record BindingSite where
  constructor Binding
  name : String
  quantity : Quantity
  span : SourceSpan
  nameSpan : SourceSpan
  definitionNameSpan : SourceSpan
  exported : Bool

||| Authored binding locations only. Does not expand expressions or admit getters.
public export
bindingSites : AuthoredDeclaration -> List BindingSite
bindingSites (Ordinary decl) =
  [Binding decl.name decl.quantity decl.span decl.nameSpan decl.definitionNameSpan decl.exported]
bindingSites (RecordItem sourceRecord) =
  [Binding sourceRecord.name.spelling Erased sourceRecord.span sourceRecord.name.span sourceRecord.name.span sourceRecord.exported,
   Binding sourceRecord.constructorName.spelling Unrestricted
     (Between sourceRecord.constructorKeyword.span.start sourceRecord.constructorName.span.finish)
     sourceRecord.constructorName.span sourceRecord.constructorName.span sourceRecord.exported,
   Binding sourceRecord.eliminatorName.spelling Unrestricted
     (Between sourceRecord.eliminatorKeyword.span.start sourceRecord.eliminatorName.span.finish)
     sourceRecord.eliminatorName.span sourceRecord.eliminatorName.span sourceRecord.exported] ++
  map (\projection => Binding projection.name.spelling Unrestricted
       (Between projection.keyword.span.start projection.field.span.finish)
       projection.name.span projection.name.span sourceRecord.exported) sourceRecord.projections

public export
ordinaryDeclarations : List AuthoredDeclaration -> List Declaration
ordinaryDeclarations [] = []
ordinaryDeclarations (Ordinary decl :: rest) = decl :: ordinaryDeclarations rest
ordinaryDeclarations (RecordItem _ :: rest) = ordinaryDeclarations rest
