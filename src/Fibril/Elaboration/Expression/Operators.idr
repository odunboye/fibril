-- Groups flat symbolic-operator chains by declared fixity into ordinary applications. This
-- runs once per declaration, before elaboration, where the visible globals (and so imported
-- fixities) are known. The result is `NApply (NApply (NRef op) left) right`, so every later
-- rule (implicit arguments, dictionary insertion, checking) sees a normal call.
module Fibril.Elaboration.Expression.Operators

import Data.List
import Data.Maybe
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Fixity
import Fibril.Source.Global
import Fibril.Source.Resolve.Error

%default total

record Pending where
  constructor Step
  operator : Token
  fixity : Fixity
  operand : Expr

applyOperator : Token -> Expr -> Expr -> Expr
applyOperator token left right =
  NApply (Between (extent left).start (extent right).finish)
    (NApply (Between (extent left).start token.span.finish) (NRef token.span token.spelling) left) right

-- Equal-level neighbours must agree on grouping; a non-associative operator never chains.
sameLevelConflict : Fixity -> Fixity -> Bool
sameLevelConflict previous next =
  previous.level == next.level && (previous.assoc /= next.assoc || next.assoc == NoAssoc)

climb : Nat -> Nat -> Maybe Fixity -> Expr -> List Pending -> Either ResolveError (Expr, List Pending)
climb fuel minimum previous left [] = Right (left, [])
climb Z minimum previous left (step :: _) =
  Left (CannotElaborate step.operator.span.start "Operator chain exceeds its grouping budget")
climb (S fuel) minimum previous left pending@(step :: later) =
  if step.fixity.level < minimum then Right (left, pending) else do
    case previous of
      Just before => if sameLevelConflict before step.fixity
        then Left (CannotElaborate step.operator.span.start
               "Operators of equal precedence cannot be mixed or chained here; add parentheses")
        else Right ()
      Nothing => Right ()
    let tighter = case step.fixity.assoc of
          RightAssoc => step.fixity.level
          _ => S step.fixity.level
    (right, remaining) <- climb fuel tighter (Just step.fixity) step.operand later
    climb fuel minimum (Just step.fixity) (applyOperator step.operator left right) remaining


group : (String -> Fixity) -> Expr -> List (Token, Expr) -> Either ResolveError Expr
group fixityOf first operands = do
  let pending = map (\(token, operand) => Step token (fixityOf token.spelling) operand) operands
  (result, _) <- climb (2 * length pending + 2) 0 Nothing first pending
  Right result

mutual
  ||| Rewrite every `NOperators` node in the expression, operands first.
  public export
  resolveExpr : (String -> Fixity) -> Expr -> Either ResolveError Expr
  resolveExpr f (NIf s a b c) = [| NIf (pure s) (resolveExpr f a) (resolveExpr f b) (resolveExpr f c) |]
  resolveExpr f (NUnitCase s a b) = [| NUnitCase (pure s) (resolveExpr f a) (resolveExpr f b) |]
  resolveExpr f (NRecEnd s a) = [| NRecEnd (pure s) (resolveExpr f a) |]
  resolveExpr f (NRecMore s a b) = [| NRecMore (pure s) (resolveExpr f a) (resolveExpr f b) |]
  resolveExpr f (NRecFold s a b c d) = [| NRecFold (pure s) (resolveExpr f a) (resolveExpr f b) (resolveExpr f c) (resolveExpr f d) |]
  resolveExpr f (NSeqType s n a) = [| NSeqType (pure s) (pure n) (resolveExpr f a) |]
  resolveExpr f (NSeqNil s a) = [| NSeqNil (pure s) (resolveExpr f a) |]
  resolveExpr f (NSeqCons s a b c) = [| NSeqCons (pure s) (resolveExpr f a) (resolveExpr f b) (resolveExpr f c) |]
  resolveExpr f (NSeqFold s a b c d) = [| NSeqFold (pure s) (resolveExpr f a) (resolveExpr f b) (resolveExpr f c) (resolveExpr f d) |]
  resolveExpr f (NNominalType s n xs a) = [| NNominalType (pure s) (pure n) (resolveList f xs) (resolveExpr f a) |]
  resolveExpr f (NNominalValue s a b) = [| NNominalValue (pure s) (resolveExpr f a) (resolveExpr f b) |]
  resolveExpr f (NNominalCase s a b c) = [| NNominalCase (pure s) (resolveExpr f a) (resolveExpr f b) (resolveExpr f c) |]
  resolveExpr f (NVariantType s arms) = [| NVariantType (pure s) (resolveVariantArms f arms) |]
  resolveExpr f (NVariantValue s a n payload) = [| NVariantValue (pure s) (resolveExpr f a) (pure n) (resolveMaybe f payload) |]
  resolveExpr f (NVariantCase s a b xs) = [| NVariantCase (pure s) (resolveExpr f a) (resolveExpr f b) (resolveList f xs) |]
  resolveExpr f (NBoxType s q a) = [| NBoxType (pure s) (pure q) (resolveExpr f a) |]
  resolveExpr f (NBoxValue s a b) = [| NBoxValue (pure s) (resolveExpr f a) (resolveExpr f b) |]
  resolveExpr f (NBoxCase s a b c) = [| NBoxCase (pure s) (resolveExpr f a) (resolveExpr f b) (resolveExpr f c) |]
  resolveExpr f (NSigma s q r n a b) = [| NSigma (pure s) (pure q) (pure r) (pure n) (resolveExpr f a) (resolveExpr f b) |]
  resolveExpr f (NPairValue s a b c) = [| NPairValue (pure s) (resolveExpr f a) (resolveExpr f b) (resolveExpr f c) |]
  resolveExpr f (NPairCase s a b c) = [| NPairCase (pure s) (resolveExpr f a) (resolveExpr f b) (resolveExpr f c) |]
  resolveExpr f (NInferCase s n a b) = [| NInferCase (pure s) (pure n) (resolveExpr f a) (resolveExpr f b) |]
  resolveExpr f (NPatternLambda s names a) = [| NPatternLambda (pure s) (pure names) (resolveExpr f a) |]
  resolveExpr f (NEquationLambda s names a b) = [| NEquationLambda (pure s) (pure names) (resolveExpr f a) (resolveExpr f b) |]
  resolveExpr f (NConstructorCase s n a b c motive) =
    [| NConstructorCase (pure s) (pure n) (resolveExpr f a) (resolveExpr f b) (resolveExpr f c) (resolveMaybe f motive) |]
  resolveExpr f (NCaseEither s a b) = [| NCaseEither (pure s) (resolveExpr f a) (resolveExpr f b) |]
  resolveExpr f (NDataCase s value motive arms) =
    [| NDataCase (pure s) (resolveExpr f value) (resolveMaybe f motive) (resolveArms f arms) |]
  resolveExpr f (NConstraintPi s q n a b) = [| NConstraintPi (pure s) (pure q) (pure n) (resolveExpr f a) (resolveExpr f b) |]
  resolveExpr f (NImplicitPi s q n a b) = [| NImplicitPi (pure s) (pure q) (pure n) (resolveExpr f a) (resolveExpr f b) |]
  resolveExpr f (NDictionaryApply s o a argument) = [| NDictionaryApply (pure s) (pure o) (resolveExpr f a) (resolveMaybe f argument) |]
  resolveExpr f (NImplementationApply s o a) = [| NImplementationApply (pure s) (pure o) (resolveExpr f a) |]
  resolveExpr f (NPi s q n a b) = [| NPi (pure s) (pure q) (pure n) (resolveExpr f a) (resolveExpr f b) |]
  resolveExpr f (NLambda s q n a b) = [| NLambda (pure s) (pure q) (pure n) (resolveExpr f a) (resolveExpr f b) |]
  resolveExpr f (NInfix s a b c) = [| NInfix (pure s) (resolveExpr f a) (resolveExpr f b) (resolveExpr f c) |]
  resolveExpr f (NOperators s first operands) = do
    first <- resolveExpr f first
    operands <- resolveOperands f operands
    group f first operands
  resolveExpr f (NApply s a b) = [| NApply (pure s) (resolveExpr f a) (resolveExpr f b) |]
  resolveExpr f (NImplicitApply s a b) = [| NImplicitApply (pure s) (resolveExpr f a) (resolveExpr f b) |]
  resolveExpr f (NSequence s a b) = [| NSequence (pure s) (resolveExpr f a) (resolveExpr f b) |]
  resolveExpr f (NDoBind s n a b c) = [| NDoBind (pure s) (pure n) (resolveExpr f a) (resolveExpr f b) (resolveExpr f c) |]
  resolveExpr f (NDoResult s a b) = [| NDoResult (pure s) (resolveExpr f a) (resolveExpr f b) |]
  resolveExpr f (NAscribe s a b) = [| NAscribe (pure s) (resolveExpr f a) (resolveExpr f b) |]
  resolveExpr f (NLet s q n a b c) = [| NLet (pure s) (pure q) (pure n) (resolveExpr f a) (resolveExpr f b) (resolveExpr f c) |]
  -- Leaves: references, literals, sorts and base types.
  resolveExpr f leaf@(NRef _ _) = Right leaf
  resolveExpr f leaf@(NQualifiedRef _ _) = Right leaf
  resolveExpr f leaf@(NSort _ _) = Right leaf
  resolveExpr f leaf@(NUnitType _) = Right leaf
  resolveExpr f leaf@(NUnitValue _) = Right leaf
  resolveExpr f leaf@(NStringType _) = Right leaf
  resolveExpr f leaf@(NStringValue _ _) = Right leaf
  resolveExpr f leaf@(NNatValue _ _) = Right leaf
  resolveExpr f leaf@(NWordValue _ _) = Right leaf
  resolveExpr f leaf@(NBoolType _) = Right leaf
  resolveExpr f leaf@(NBoolValue _ _) = Right leaf
  resolveExpr f leaf@(NRecType _ _) = Right leaf
  resolveExpr f leaf@(NDataType _ _) = Right leaf
  resolveExpr f leaf@(NDataCon _ _ _ _) = Right leaf

  resolveList : (String -> Fixity) -> List Expr -> Either ResolveError (List Expr)
  resolveList f [] = Right []
  resolveList f (x :: xs) = [| resolveExpr f x :: resolveList f xs |]

  resolveMaybe : (String -> Fixity) -> Maybe Expr -> Either ResolveError (Maybe Expr)
  resolveMaybe f Nothing = Right Nothing
  resolveMaybe f (Just x) = Just <$> resolveExpr f x

  resolveVariantArms : (String -> Fixity) -> List (Maybe (Quantity, Expr)) -> Either ResolveError (List (Maybe (Quantity, Expr)))
  resolveVariantArms f [] = Right []
  resolveVariantArms f (Nothing :: rest) = [| pure Nothing :: resolveVariantArms f rest |]
  resolveVariantArms f (Just (q, x) :: rest) = [| (Just . MkPair q <$> resolveExpr f x) :: resolveVariantArms f rest |]

  resolveArms : (String -> Fixity) -> List (Token, List Token, Expr) -> Either ResolveError (List (Token, List Token, Expr))
  resolveArms f [] = Right []
  resolveArms f ((constructor, binders, body) :: rest) =
    [| ((\resolved => (constructor, binders, resolved)) <$> resolveExpr f body) :: resolveArms f rest |]

  resolveOperands : (String -> Fixity) -> List (Token, Expr) -> Either ResolveError (List (Token, Expr))
  resolveOperands f [] = Right []
  resolveOperands f ((token, operand) :: rest) =
    [| ((\resolved => (token, resolved)) <$> resolveExpr f operand) :: resolveOperands f rest |]

||| Declared fixity of a visible global; undeclared operators get the default.
public export
globalFixity : List GlobalDefinition -> String -> Fixity
globalFixity globals name =
  fromMaybe defaultFixity (find (\entry => entry.name == name) globals >>= \entry => entry.fixity)
