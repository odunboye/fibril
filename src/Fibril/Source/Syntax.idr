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
  | NBoxType SourceSpan Quantity Expr
  | NBoxValue SourceSpan Expr Expr
  | NBoxCase SourceSpan Expr Expr Expr
  | NSigma SourceSpan Quantity Quantity String Expr Expr
  | NPairValue SourceSpan Expr Expr Expr
  | NPairCase SourceSpan Expr Expr Expr
  | NInferCase SourceSpan Nat Expr Expr
  | NPatternLambda SourceSpan (List Token) Expr
  | NConstructorCase SourceSpan Nat Expr Expr Expr (Maybe Expr)
  | NConstraintPi SourceSpan Quantity String Expr Expr
  | NDictionaryApply SourceSpan SourceSpan Expr (Maybe Expr)
  | NImplementationApply SourceSpan SourceSpan Expr
  | NPi SourceSpan Quantity String Expr Expr
  | NLambda SourceSpan Quantity String Expr Expr
  | NApply SourceSpan Expr Expr
  | NSequence SourceSpan Expr Expr
  | NDoBind SourceSpan String Expr Expr Expr
  | NDoResult SourceSpan Expr Expr
  | NAscribe SourceSpan Expr Expr
  | NLet SourceSpan Quantity String Expr Expr Expr

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
extent (NBoxType span _ _) = span
extent (NBoxValue span _ _) = span
extent (NBoxCase span _ _ _) = span
extent (NSigma span _ _ _ _ _) = span
extent (NPairValue span _ _ _) = span
extent (NPairCase span _ _ _) = span
extent (NInferCase span _ _ _) = span
extent (NPatternLambda span _ _) = span
extent (NConstructorCase span _ _ _ _ _) = span
extent (NConstraintPi span _ _ _ _) = span
extent (NDictionaryApply span _ _ _) = span
extent (NImplementationApply span _ _) = span
extent (NPi span _ _ _ _) = span
extent (NLambda span _ _ _ _) = span
extent (NApply span _ _) = span
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
withExtent span (NBoxType _ q ty) = NBoxType span q ty
withExtent span (NBoxValue _ ty value) = NBoxValue span ty value
withExtent span (NBoxCase _ motive value branch) = NBoxCase span motive value branch
withExtent span (NSigma _ q r name domain body) = NSigma span q r name domain body
withExtent span (NPairValue _ ty first second) = NPairValue span ty first second
withExtent span (NPairCase _ motive value branch) = NPairCase span motive value branch
withExtent span (NInferCase _ arity value branch) = NInferCase span arity value branch
withExtent span (NPatternLambda _ names body) = NPatternLambda span names body
withExtent span (NConstructorCase _ arity constructor value branch motive) = NConstructorCase span arity constructor value branch motive
withExtent span (NConstraintPi _ q name domain body) = NConstraintPi span q name domain body
withExtent span (NDictionaryApply _ origin function argument) = NDictionaryApply span origin function argument
withExtent span (NImplementationApply _ origin function) = NImplementationApply span origin function
withExtent span (NPi _ q name domain body) = NPi span q name domain body
withExtent span (NLambda _ q name domain body) = NLambda span q name domain body
withExtent span (NApply _ function argument) = NApply span function argument
withExtent span (NSequence _ first rest) = NSequence span first rest
withExtent span (NDoBind _ name domain action body) = NDoBind span name domain action body
withExtent span (NDoResult _ result body) = NDoResult span result body
withExtent span (NAscribe _ term expected) = NAscribe span term expected
withExtent span (NLet _ q name expected value body) = NLet span q name expected value body
