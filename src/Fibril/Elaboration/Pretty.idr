-- Readable named IR, not a round-trippable source formatter.
module Fibril.Elaboration.Pretty

import Fibril.Core.Quantity
import Fibril.Source.Syntax

%default total

node : String -> List String -> String
node name arguments = "(" ++ name ++ concatMap (" " ++) arguments ++ ")"

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
renderExpr (NPi _ q name domain body) = node "Pi" [show q, name, renderExpr domain, renderExpr body]
renderExpr (NLambda _ q name domain body) = node "lambda" [show q, name, renderExpr domain, renderExpr body]
renderExpr (NSigma _ q r name domain body) = node "Sigma" [show q, show r, name, renderExpr domain, renderExpr body]
renderExpr (NPairValue _ ty first second) = node "pair" [renderExpr ty, renderExpr first, renderExpr second]
renderExpr (NPairCase _ motive value branch) = node "pair-case" [renderExpr motive, renderExpr value, renderExpr branch]
renderExpr (NApply _ function argument) = node "apply" [renderExpr function, renderExpr argument]
renderExpr (NSequence _ first rest) = node "sequence" [renderExpr first, renderExpr rest]
renderExpr (NDoBind _ name ty action body) = node "do-bind" [name, renderExpr ty, renderExpr action, renderExpr body]
renderExpr (NDoResult _ result body) = node "do-result" [renderExpr result, renderExpr body]
renderExpr (NAscribe _ value ty) = node "ascribe" [renderExpr value, renderExpr ty]
renderExpr (NLet _ q name ty value body) = node "let" [show q, name, renderExpr ty, renderExpr value, renderExpr body]
