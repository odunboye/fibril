-- Named, spanned expressions; these are not scoped or type-checked.
module Fibril.Source.Syntax

import Fibril.Core.Quantity
import Fibril.Source.Lexer

%default total

||| Initial named expression grammar, separate from the trusted core syntax.
public export
data Expr
  = NRef SourceSpan String
  | NSort SourceSpan Nat
  | NPi SourceSpan Quantity String Expr Expr
  | NLambda SourceSpan Quantity String Expr Expr
  | NApply SourceSpan Expr Expr
  | NAscribe SourceSpan Expr Expr

||| Recover the complete syntactic extent of an expression.
public export
extent : Expr -> SourceSpan
extent (NRef span _) = span
extent (NSort span _) = span
extent (NPi span _ _ _ _) = span
extent (NLambda span _ _ _ _) = span
extent (NApply span _ _) = span
extent (NAscribe span _ _) = span

||| Include grouping parentheses without changing expression meaning.
public export
withExtent : SourceSpan -> Expr -> Expr
withExtent span (NRef _ name) = NRef span name
withExtent span (NSort _ level) = NSort span level
withExtent span (NPi _ q name domain body) = NPi span q name domain body
withExtent span (NLambda _ q name domain body) = NLambda span q name domain body
withExtent span (NApply _ function argument) = NApply span function argument
withExtent span (NAscribe _ term expected) = NAscribe span term expected
