-- Readable named IR, not a round-trippable source formatter.
module Fibril.Elaboration.Pretty

import Fibril.Core.Quantity
import Fibril.Source.Lexer
import Fibril.Source.Syntax

%default total

node : String -> List String -> String
node name arguments = "(" ++ name ++ concatMap (" " ++) arguments ++ ")"

mutual
  public export
  renderExpr : Expr -> String
  renderExpr (NRef _ name) = name
  renderExpr (NQualifiedRef _ name) = "global[" ++ name ++ "]"
  renderExpr (NSort _ level) = "Type" ++ show level
  renderExpr (NUnitType _) = "Unit"
  renderExpr (NUnitValue _) = "()"
  renderExpr (NStringType _) = "String"
  renderExpr (NStringValue _ value) = show value
  renderExpr (NBoolType _) = "Bool"
  renderExpr (NBoolValue _ value) = if value then "True" else "False"
  renderExpr (NIf _ condition yes no) = node "if" [renderExpr condition, renderExpr yes, renderExpr no]
  renderExpr (NUnitCase _ value body) = node "unit-case" [renderExpr value, renderExpr body]
  renderExpr (NConstraintPi _ q name domain body) = node "constraint-pi" [show q, name, renderExpr domain, renderExpr body]
  renderExpr (NImplementationApply _ _ function) = node "implementation-apply" [renderExpr function]
  renderExpr (NDictionaryApply _ _ function argument) = node "dictionary-apply" [renderExpr function, (case argument of Nothing => "local-unique"; Just value => renderExpr value)]
  renderExpr (NPi _ q name domain body) = node "Pi" [show q, name, renderExpr domain, renderExpr body]
  renderExpr (NLambda _ q name domain body) = node "lambda" [show q, name, renderExpr domain, renderExpr body]
  renderExpr (NSigma _ q r name domain body) = node "Sigma" [show q, show r, name, renderExpr domain, renderExpr body]
  renderExpr (NPairValue _ ty first second) = node "pair" [renderExpr ty, renderExpr first, renderExpr second]
  renderExpr (NNominalType _ key indices shape) = node "nominal-type" [show key, node "indices" (renderTerms indices), renderExpr shape]
  renderExpr (NNominalValue _ ty value) = node "nominal-value" [renderExpr ty, renderExpr value]
  renderExpr (NNominalCase _ motive value branch) = node "nominal-case" [renderExpr motive, renderExpr value, renderExpr branch]
  renderExpr (NVariantType _ arms) = node "variant-type" (renderArms arms)
  renderExpr (NVariantValue _ ty tag payload) = node "variant-value" [renderExpr ty, show tag, (case payload of Nothing => "nullary"; Just value => renderExpr value)]
  renderExpr (NVariantCase _ motive value branches) = node "variant-case" [renderExpr motive, renderExpr value, node "branches" (renderTerms branches)]
  renderExpr (NBoxType _ q ty) = node "box-type" [show q, renderExpr ty]
  renderExpr (NBoxValue _ ty value) = node "box-value" [renderExpr ty, renderExpr value]
  renderExpr (NBoxCase _ motive value branch) = node "box-case" [renderExpr motive, renderExpr value, renderExpr branch]
  renderExpr (NEquationLambda _ names signature body) = node "equation" [node "parameters" (map spelling names), renderExpr signature, renderExpr body]
  renderExpr (NPatternLambda _ names body) = node "infer-field-binders" [node "names" (map spelling names), renderExpr body]
  renderExpr (NDataCase _ value motive arms) = node "data-case" [renderExpr value, renderExpr motive, node "branches" (renderDataArms arms)]
  renderExpr (NConstructorCase _ arity constructor value branch motive) = node "constructor-record-case" [show arity, renderExpr constructor, renderExpr value, renderExpr branch, (case motive of Nothing => "infer"; Just result => renderExpr result)]
  renderExpr (NInferCase _ arity value branch) = node "infer-record-case" [show arity, renderExpr value, renderExpr branch]
  renderExpr (NPairCase _ motive value branch) = node "pair-case" [renderExpr motive, renderExpr value, renderExpr branch]
  renderExpr (NInfix _ function left right) = node "infix-apply" [renderExpr function, renderExpr left, renderExpr right]
  renderExpr (NApply _ function argument) = node "apply" [renderExpr function, renderExpr argument]
  renderExpr (NSequence _ first rest) = node "sequence" [renderExpr first, renderExpr rest]
  renderExpr (NDoBind _ name ty action body) = node "do-bind" [name, renderExpr ty, renderExpr action, renderExpr body]
  renderExpr (NDoResult _ result body) = node "do-result" [renderExpr result, renderExpr body]
  renderExpr (NAscribe _ value ty) = node "ascribe" [renderExpr value, renderExpr ty]
  renderExpr (NLet _ q name ty value body) = node "let" [show q, name, renderExpr ty, renderExpr value, renderExpr body]

  renderDataArms : List (Token, Maybe Token, Expr) -> List String
  renderDataArms [] = []
  renderDataArms ((name, binder, body) :: rest) =
    node "arm" [name.spelling, maybe "nullary" spelling binder, renderExpr body] :: renderDataArms rest

  renderTerms : List Expr -> List String
  renderTerms [] = []
  renderTerms (x :: xs) = renderExpr x :: renderTerms xs

  renderArms : List (Maybe (Quantity, Expr)) -> List String
  renderArms [] = []
  renderArms (Nothing :: xs) = "nullary" :: renderArms xs
  renderArms (Just (q, ty) :: xs) = node "payload" [show q, renderExpr ty] :: renderArms xs
