-- Named, spanned expressions; these are not scoped or type-checked.
module Fibril.Source.Syntax

import Fibril.Core.Quantity
import Fibril.Source.Lexer

%default total

||| Initial named expression grammar, separate from the trusted core syntax.
public export
data Expr
  = NRef SourceSpan String
  | NQualifiedRef SourceSpan String
  | NSort SourceSpan Nat
  | NUnitType SourceSpan
  | NUnitValue SourceSpan
  | NStringType SourceSpan
  | NStringValue SourceSpan String
  | NBoolType SourceSpan
  | NBoolValue SourceSpan Bool
  | NIf SourceSpan Expr Expr Expr
  | NUnitCase SourceSpan Expr Expr
  | NRecType SourceSpan String
  | NRecEnd SourceSpan Expr
  | NRecMore SourceSpan Expr Expr
  | NRecFold SourceSpan Expr Expr Expr Expr
  | NSeqType SourceSpan String Expr
  | NSeqNil SourceSpan Expr
  | NSeqCons SourceSpan Expr Expr Expr
  | NSeqFold SourceSpan Expr Expr Expr Expr
  | NNominalType SourceSpan String (List Expr) Expr
  | NNominalValue SourceSpan Expr Expr
  | NNominalCase SourceSpan Expr Expr Expr
  | NVariantType SourceSpan (List (Maybe (Quantity, Expr)))
  | NVariantValue SourceSpan Expr Nat (Maybe Expr)
  | NVariantCase SourceSpan Expr Expr (List Expr)
  | NBoxType SourceSpan Quantity Expr
  | NBoxValue SourceSpan Expr Expr
  | NBoxCase SourceSpan Expr Expr Expr
  | NSigma SourceSpan Quantity Quantity String Expr Expr
  | NPairValue SourceSpan Expr Expr Expr
  | NPairCase SourceSpan Expr Expr Expr
  | NInferCase SourceSpan Nat Expr Expr
  | NPatternLambda SourceSpan (List Token) Expr
  | NEquationLambda SourceSpan (List Token) Expr Expr
  | NConstructorCase SourceSpan Nat Expr Expr Expr (Maybe Expr)
  | NDataCase SourceSpan Expr (Maybe Expr) (List (Token, Maybe Token, Expr))
  | NConstraintPi SourceSpan Quantity String Expr Expr
  | NImplicitPi SourceSpan Quantity String Expr Expr
  | NDictionaryApply SourceSpan SourceSpan Expr (Maybe Expr)
  | NImplementationApply SourceSpan SourceSpan Expr
  | NPi SourceSpan Quantity String Expr Expr
  | NLambda SourceSpan Quantity String Expr Expr
  | NInfix SourceSpan Expr Expr Expr
  | NApply SourceSpan Expr Expr
  | NImplicitApply SourceSpan Expr Expr
  | NSequence SourceSpan Expr Expr
  | NDoBind SourceSpan String Expr Expr Expr
  | NDoResult SourceSpan Expr Expr
  | NAscribe SourceSpan Expr Expr
  | NLet SourceSpan Quantity String Expr Expr Expr

||| Count only the consecutive source-authored leading implicit binders.
public export
implicitPrefixCount : Expr -> Nat
implicitPrefixCount (NImplicitPi _ _ _ _ body) = S (implicitPrefixCount body)
implicitPrefixCount _ = 0

||| Source application steps retain authored argument spans and visibility.
public export
data CallArgument = OrdinaryArgument SourceSpan Expr | BracedArgument SourceSpan Expr

||| Collect one left-associated spine without crossing other expression forms.
public export
applicationSpine : Expr -> (Expr, List CallArgument)
applicationSpine expression = gather expression []
  where
    gather : Expr -> List CallArgument -> (Expr, List CallArgument)
    gather (NApply span function argument) rest = gather function (OrdinaryArgument span argument :: rest)
    gather (NImplicitApply span function argument) rest = gather function (BracedArgument span argument :: rest)
    gather head rest = (head, rest)

||| Recover the complete syntactic extent of an expression.
public export
extent : Expr -> SourceSpan
extent (NRef span _) = span
extent (NQualifiedRef span _) = span
extent (NSort span _) = span
extent (NUnitType span) = span
extent (NUnitValue span) = span
extent (NStringType span) = span
extent (NStringValue span _) = span
extent (NBoolType span) = span
extent (NBoolValue span _) = span
extent (NIf span _ _ _) = span
extent (NUnitCase span _ _) = span
extent (NRecType span _) = span
extent (NRecEnd span _) = span
extent (NRecMore span _ _) = span
extent (NRecFold span _ _ _ _) = span
extent (NSeqType span _ _) = span
extent (NSeqNil span _) = span
extent (NSeqCons span _ _ _) = span
extent (NSeqFold span _ _ _ _) = span
extent (NNominalType span _ _ _) = span
extent (NNominalValue span _ _) = span
extent (NNominalCase span _ _ _) = span
extent (NVariantType span _) = span
extent (NVariantValue span _ _ _) = span
extent (NVariantCase span _ _ _) = span
extent (NBoxType span _ _) = span
extent (NBoxValue span _ _) = span
extent (NBoxCase span _ _ _) = span
extent (NSigma span _ _ _ _ _) = span
extent (NPairValue span _ _ _) = span
extent (NPairCase span _ _ _) = span
extent (NInferCase span _ _ _) = span
extent (NPatternLambda span _ _) = span
extent (NEquationLambda span _ _ _) = span
extent (NConstructorCase span _ _ _ _ _) = span
extent (NDataCase span _ _ _) = span
extent (NConstraintPi span _ _ _ _) = span
extent (NImplicitPi span _ _ _ _) = span
extent (NDictionaryApply span _ _ _) = span
extent (NImplementationApply span _ _) = span
extent (NPi span _ _ _ _) = span
extent (NLambda span _ _ _ _) = span
extent (NInfix span _ _ _) = span
extent (NApply span _ _) = span
extent (NImplicitApply span _ _) = span
extent (NSequence span _ _) = span
extent (NDoBind span _ _ _ _) = span
extent (NDoResult span _ _) = span
extent (NAscribe span _ _) = span
extent (NLet span _ _ _ _ _) = span

||| Include grouping parentheses without changing expression meaning.
public export
withExtent : SourceSpan -> Expr -> Expr
withExtent span (NRef _ name) = NRef span name
withExtent span (NQualifiedRef _ name) = NQualifiedRef span name
withExtent span (NSort _ level) = NSort span level
withExtent span (NUnitType _) = NUnitType span
withExtent span (NUnitValue _) = NUnitValue span
withExtent span (NStringType _) = NStringType span
withExtent span (NStringValue _ value) = NStringValue span value
withExtent span (NBoolType _) = NBoolType span
withExtent span (NBoolValue _ value) = NBoolValue span value
withExtent span (NIf _ condition yes no) = NIf span condition yes no
withExtent span (NUnitCase _ scrutinee body) = NUnitCase span scrutinee body
withExtent span (NRecType _ key) = NRecType span key
withExtent span (NRecEnd _ ty) = NRecEnd span ty
withExtent span (NRecMore _ ty tail) = NRecMore span ty tail
withExtent span (NRecFold _ motive base next value) = NRecFold span motive base next value
withExtent span (NSeqType _ key element) = NSeqType span key element
withExtent span (NSeqNil _ ty) = NSeqNil span ty
withExtent span (NSeqCons _ ty head tail) = NSeqCons span ty head tail
withExtent span (NSeqFold _ motive base next value) = NSeqFold span motive base next value
withExtent span (NNominalType _ key indices shape) = NNominalType span key indices shape
withExtent span (NNominalValue _ ty value) = NNominalValue span ty value
withExtent span (NNominalCase _ motive value branch) = NNominalCase span motive value branch
withExtent span (NVariantType _ arms) = NVariantType span arms
withExtent span (NVariantValue _ ty tag payload) = NVariantValue span ty tag payload
withExtent span (NVariantCase _ motive value branches) = NVariantCase span motive value branches
withExtent span (NBoxType _ q ty) = NBoxType span q ty
withExtent span (NBoxValue _ ty value) = NBoxValue span ty value
withExtent span (NBoxCase _ motive value branch) = NBoxCase span motive value branch
withExtent span (NSigma _ q r name domain body) = NSigma span q r name domain body
withExtent span (NPairValue _ ty first second) = NPairValue span ty first second
withExtent span (NPairCase _ motive value branch) = NPairCase span motive value branch
withExtent span (NInferCase _ arity value branch) = NInferCase span arity value branch
withExtent span (NPatternLambda _ names body) = NPatternLambda span names body
withExtent span (NEquationLambda _ names signature body) = NEquationLambda span names signature body
withExtent span (NConstructorCase _ arity constructor value branch motive) = NConstructorCase span arity constructor value branch motive
withExtent span (NDataCase _ value motive arms) = NDataCase span value motive arms
withExtent span (NConstraintPi _ q name domain body) = NConstraintPi span q name domain body
withExtent span (NImplicitPi _ q name domain body) = NImplicitPi span q name domain body
withExtent span (NDictionaryApply _ origin function argument) = NDictionaryApply span origin function argument
withExtent span (NImplementationApply _ origin function) = NImplementationApply span origin function
withExtent span (NPi _ q name domain body) = NPi span q name domain body
withExtent span (NLambda _ q name domain body) = NLambda span q name domain body
withExtent span (NInfix _ function left right) = NInfix span function left right
withExtent span (NApply _ function argument) = NApply span function argument
withExtent span (NImplicitApply _ function argument) = NImplicitApply span function argument
withExtent span (NSequence _ first rest) = NSequence span first rest
withExtent span (NDoBind _ name domain action body) = NDoBind span name domain action body
withExtent span (NDoResult _ result body) = NDoResult span result body
withExtent span (NAscribe _ term expected) = NAscribe span term expected
withExtent span (NLet _ q name expected value body) = NLet span q name expected value body
