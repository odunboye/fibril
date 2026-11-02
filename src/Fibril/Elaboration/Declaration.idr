-- Explicit record lowering and admission; generated IR still needs core checking.
module Fibril.Elaboration.Declaration

import Data.List
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Declaration.Syntax

%default total

public export
record ElaborationError where
  constructor ElaborationFailure
  position : Position
  message : String

public export
Show ElaborationError where
  show err = show err.position ++ ": " ++ err.message

validateProjection : RecordField -> RecordField -> RecordProjection -> Either ElaborationError ()
validateProjection first second projection = do
  let selected = if projection.field.spelling == first.token.spelling then first else second
  let discarded = if projection.field.spelling == first.token.spelling then second else first
  if not (elem projection.field.spelling [first.token.spelling, second.token.spelling])
     then Left (ElaborationFailure projection.field.span.start "Unknown projected field") else Right ()
  if not (allows selected.quantity Linear)
     then Left (ElaborationFailure projection.field.span.start "Erased fields cannot be projected as runtime values") else Right ()
  if not (allows discarded.quantity Erased)
     then Left (ElaborationFailure projection.field.span.start "Projection would discard a linear field; consume both fields with a pattern instead") else Right ()

parameterPis : SourceSpan -> List RecordParameter -> Expr -> Expr
parameterPis region [] body = body
parameterPis region (parameter :: rest) body =
  NPi region Erased parameter.name parameter.domain (parameterPis region rest body)

parameterLambdas : SourceSpan -> List RecordParameter -> Expr -> Expr
parameterLambdas region [] body = body
parameterLambdas region (parameter :: rest) body =
  NLambda region Erased parameter.name parameter.domain (parameterLambdas region rest body)

applyParameters : SourceSpan -> Expr -> List RecordParameter -> Expr
applyParameters region function [] = function
applyParameters region function (parameter :: rest) =
  applyParameters region (NApply region function (NRef parameter.span parameter.name)) rest

projectionDeclaration : SourceSpan -> Token -> List RecordParameter -> RecordField -> RecordField ->
                        RecordProjection -> Declaration
projectionDeclaration region recordName params first second projection =
  let typeRef = applyParameters region (NQualifiedRef recordName.span recordName.spelling) params
      x = first.token.spelling
      y = second.token.spelling
      xRef = NRef first.token.span x
      yRef = NRef second.token.span y
      argument = "$projection.record"
      self = "$projection.self"
      argumentRef = NRef projection.name.span argument
      selfRef = NRef projection.name.span self
      lam = \q, name, ty, body => NLambda region q name ty body
      app = \f, value => NApply region f value
      branch = \body => lam first.quantity x first.ty (lam second.quantity y second.ty body)
      -- This extraction occurs only in types/motives. Erased checking may
      -- inspect an erased field, but it is never emitted as runtime data.
      firstOf = \value => NPairCase region (lam Erased self typeRef first.ty) value (branch xRef)
      secondType = \value => app (lam Erased x first.ty second.ty) (firstOf value)
      selectedFirst = projection.field.spelling == first.token.spelling
      result = if selectedFirst then first.ty else secondType argumentRef
      motive = lam Erased self typeRef (if selectedFirst then first.ty else secondType selfRef)
      ty = NPi region Linear argument typeRef result
      value = lam Linear argument typeRef
                (NPairCase region motive argumentRef (branch (if selectedFirst then xRef else yRef)))
   in Declared True (Between projection.keyword.span.start projection.field.span.finish)
        projection.name.span projection.name.span False Unrestricted projection.name.spelling
        (parameterPis region params ty) (parameterLambdas region params value)

-- Generated binders cannot be captured by any legal source identifier.
-- Global-only references use the resolver's separate qualified namespace,
-- even for these unqualified generated declaration names.
recordDeclarations : SourceSpan -> Token -> Nat -> List RecordParameter -> Token -> Token -> Token -> Token ->
                     RecordField -> RecordField -> List RecordProjection -> List Declaration
recordDeclarations region name level params constructorKeyword constructorName eliminatorKeyword eliminatorName first second projections =
  let typeRef = applyParameters region (NQualifiedRef name.span name.spelling) params
      ctorRef = applyParameters region (NQualifiedRef constructorName.span constructorName.spelling) params
      x = first.token.spelling
      y = second.token.spelling
      xRef = NRef first.token.span x
      yRef = NRef second.token.span y
      p = "$record.motive"
      value = "$record.value"
      next = "$record.branch"
      self = "$record.self"
      pRef = NRef eliminatorName.span p
      valueRef = NRef eliminatorName.span value
      nextRef = NRef eliminatorName.span next
      bind = \q, binder, ty, body => NPi region q binder ty body
      lam = \q, binder, ty, body => NLambda region q binder ty body
      app = \f, arg => NApply region f arg
      fields = \body => bind first.quantity x first.ty (bind second.quantity y second.ty body)
      sigma = NSigma region first.quantity second.quantity x first.ty second.ty
      ctorType = fields typeRef
      ctorValue = lam first.quantity x first.ty (lam second.quantity y second.ty (NPairValue region typeRef xRef yRef))
      motiveType = bind Erased self typeRef (NSort eliminatorName.span level)
      branchType = fields (app pRef (app (app ctorRef xRef) yRef))
      elimType = bind Erased p motiveType (bind Linear value typeRef (bind Linear next branchType (app pRef valueRef)))
      elimValue = lam Erased p motiveType (lam Linear value typeRef (lam Linear next branchType (NPairCase region pRef valueRef nextRef)))
   in [ Declared True region name.span name.span False Erased name.spelling
          (parameterPis region params (NSort name.span level)) (parameterLambdas region params sigma),
        Declared True (Between constructorKeyword.span.start constructorName.span.finish)
          constructorName.span constructorName.span False Unrestricted constructorName.spelling
          (parameterPis region params ctorType) (parameterLambdas region params ctorValue),
        Declared True (Between eliminatorKeyword.span.start eliminatorName.span.finish)
          eliminatorName.span eliminatorName.span False Unrestricted eliminatorName.spelling
          (parameterPis region params elimType) (parameterLambdas region params elimValue) ] ++
      map (projectionDeclaration region name params first second) projections


validateParameters : List String -> List RecordParameter -> Either ElaborationError ()
validateParameters seen [] = Right ()
validateParameters seen (parameter :: rest) = do
  if parameter.quantity /= Erased || parameter.name == "_"
     then Left (ElaborationFailure parameter.span.start "Record parameters require explicit 0 and a referenceable name")
     else Right ()
  if elem parameter.name seen
     then Left (ElaborationFailure parameter.span.start "Duplicate record parameter") else Right ()
  validateParameters (parameter.name :: seen) rest

lowerRecord : RecordDeclaration -> Either ElaborationError (List Declaration)
lowerRecord sourceRecord = do
  if length sourceRecord.params > 8 || length sourceRecord.projections > 2
     then Left (ElaborationFailure sourceRecord.span.start "Record parameter/projection admission budget exhausted") else Right ()
  validateParameters [] sourceRecord.params
  if sourceRecord.first.token.spelling == sourceRecord.second.token.spelling
     then Left (ElaborationFailure sourceRecord.second.token.span.start "Duplicate record field") else Right ()
  traverse_ (\field => if field.token.spelling == "_"
                        then Left (ElaborationFailure field.token.span.start "Record fields need referenceable names")
                        else Right ()) [sourceRecord.first, sourceRecord.second]
  traverse_ (\field => if any (\p => p.name == field.token.spelling) sourceRecord.params
                        then Left (ElaborationFailure field.token.span.start "Record fields must not shadow record parameters")
                        else Right ()) [sourceRecord.first, sourceRecord.second]
  traverse_ (validateProjection sourceRecord.first sourceRecord.second) sourceRecord.projections
  Right (map (\decl => { exported := sourceRecord.exported } decl)
    (recordDeclarations sourceRecord.span sourceRecord.name sourceRecord.level sourceRecord.params sourceRecord.constructorKeyword
      sourceRecord.constructorName sourceRecord.eliminatorKeyword sourceRecord.eliminatorName sourceRecord.first sourceRecord.second sourceRecord.projections))

admit : Nat -> List String -> List Declaration -> Either ElaborationError (Nat, List String)
admit slots seen [] = Right (slots, seen)
admit Z seen (decl :: _) = Left (ElaborationFailure decl.nameSpan.start "Elaborated declaration budget exhausted")
admit (S slots) seen (decl :: rest) =
  if elem decl.name seen then Left (ElaborationFailure decl.nameSpan.start ("Duplicate declaration " ++ show decl.name))
     else admit slots (decl.name :: seen) rest

lower : Nat -> List String -> List AuthoredDeclaration -> Either ElaborationError (List Declaration)
lower slots seen [] = Right []
lower slots seen (item :: rest) = do
  declarations <- case item of
    Ordinary decl => Right [decl]
    RecordItem sourceRecord => lowerRecord sourceRecord
  (remaining, names) <- admit slots seen declarations
  following <- lower remaining names rest
  Right (declarations ++ following)

||| Ordinary headerless declarations retain their nonrecursive typed-let lowering.
public export
lowerDeclarations : Position -> List Declaration -> Expr
lowerDeclarations end [] = NRef (Between end end) "main"
lowerDeclarations end (decl :: rest) =
  NLet (Between decl.span.start end) decl.quantity decl.name decl.expected decl.value
       (lowerDeclarations end rest)

||| Pure, bounded lowering. This validates declaration policy, not core typing.
public export
elaborateDeclarations : Nat -> List AuthoredDeclaration -> Either ElaborationError (List Declaration)
elaborateDeclarations budget = lower budget []
