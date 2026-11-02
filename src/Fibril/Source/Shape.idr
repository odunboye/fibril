-- Structural parser-result comparison, deliberately ignoring source positions.
module Fibril.Source.Shape

import Fibril.Core.Quantity
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Document
import Fibril.Source.Declaration.Syntax

%default total

sameList : (a -> b -> Bool) -> List a -> List b -> Bool
sameList eq [] [] = True
sameList eq (x :: xs) (y :: ys) = eq x y && sameList eq xs ys
sameList _ _ _ = False

public export
sameExpr : Expr -> Expr -> Bool
sameExpr (NRef _ a) (NRef _ b) = a == b
sameExpr (NQualifiedRef _ a) (NQualifiedRef _ b) = a == b
sameExpr (NSort _ a) (NSort _ b) = a == b
sameExpr (NUnitType _) (NUnitType _) = True
sameExpr (NUnitValue _) (NUnitValue _) = True
sameExpr (NStringType _) (NStringType _) = True
sameExpr (NStringValue _ a) (NStringValue _ b) = a == b
sameExpr (NBoolType _) (NBoolType _) = True
sameExpr (NBoolValue _ a) (NBoolValue _ b) = a == b
sameExpr (NIf _ a b c) (NIf _ x y z) = sameExpr a x && sameExpr b y && sameExpr c z
sameExpr (NUnitCase _ a b) (NUnitCase _ x y) = sameExpr a x && sameExpr b y
sameExpr (NPi _ q name a b) (NPi _ r other x y) = q == r && name == other && sameExpr a x && sameExpr b y
sameExpr (NLambda _ q name a b) (NLambda _ r other x y) = q == r && name == other && sameExpr a x && sameExpr b y
sameExpr (NSigma _ q r name a b) (NSigma _ s t other x y) = q == s && r == t && name == other && sameExpr a x && sameExpr b y
sameExpr (NPairValue _ a b c) (NPairValue _ x y z) = sameExpr a x && sameExpr b y && sameExpr c z
sameExpr (NBoxType _ q a) (NBoxType _ r b) = q == r && sameExpr a b
sameExpr (NBoxValue _ a b) (NBoxValue _ x y) = sameExpr a x && sameExpr b y
sameExpr (NBoxCase _ a b c) (NBoxCase _ x y z) = sameExpr a x && sameExpr b y && sameExpr c z
sameExpr (NPatternLambda _ names body) (NPatternLambda _ other value) = map spelling names == map spelling other && sameExpr body value
sameExpr (NConstructorCase _ n c a b Nothing) (NConstructorCase _ m d x y Nothing) =
  n == m && sameExpr c d && sameExpr a x && sameExpr b y
sameExpr (NConstructorCase _ n c a b (Just p)) (NConstructorCase _ m d x y (Just q)) =
  n == m && sameExpr c d && sameExpr a x && sameExpr b y && sameExpr p q
sameExpr (NInferCase _ n a b) (NInferCase _ m x y) = n == m && sameExpr a x && sameExpr b y
sameExpr (NPairCase _ a b c) (NPairCase _ x y z) = sameExpr a x && sameExpr b y && sameExpr c z
sameExpr (NApply _ a b) (NApply _ x y) = sameExpr a x && sameExpr b y
sameExpr (NSequence _ a b) (NSequence _ x y) = sameExpr a x && sameExpr b y
sameExpr (NDoBind _ name a b c) (NDoBind _ other x y z) = name == other && sameExpr a x && sameExpr b y && sameExpr c z
sameExpr (NDoResult _ a b) (NDoResult _ x y) = sameExpr a x && sameExpr b y
sameExpr (NAscribe _ a b) (NAscribe _ x y) = sameExpr a x && sameExpr b y
sameExpr (NLet _ q name a b c) (NLet _ r other x y z) = q == r && name == other && sameExpr a x && sameExpr b y && sameExpr c z
sameExpr _ _ = False

sameParameter : RecordParameter -> RecordParameter -> Bool
sameParameter a b = a.quantity == b.quantity && a.name == b.name && sameExpr a.domain b.domain

sameField : RecordField -> RecordField -> Bool
sameField a b = a.quantity == b.quantity && a.token.spelling == b.token.spelling && sameExpr a.ty b.ty

sameProjection : RecordProjection -> RecordProjection -> Bool
sameProjection a b = a.name.spelling == b.name.spelling && a.field.spelling == b.field.spelling

sameAuthored : AuthoredDeclaration -> AuthoredDeclaration -> Bool
sameAuthored (ImplementationBlock a) (ImplementationBlock b) =
  a.name.spelling == b.name.spelling && a.exported == b.exported && sameExpr a.target b.target &&
    sameList (\x, y => x.name.spelling == y.name.spelling && sameExpr x.value y.value) a.methods b.methods
sameAuthored (Ordinary a) (Ordinary b) = a.name == b.name && a.quantity == b.quantity &&
  a.exported == b.exported && a.generated == b.generated && a.dictionary == b.dictionary && sameExpr a.expected b.expected && sameExpr a.value b.value
sameAuthored (ImplementationItem a) (ImplementationItem b) = a.name == b.name && a.quantity == b.quantity &&
  a.exported == b.exported && a.generated == b.generated && a.dictionary == b.dictionary && sameExpr a.expected b.expected && sameExpr a.value b.value
sameAuthored (RecordItem a) (RecordItem b) = a.name.spelling == b.name.spelling && a.level == b.level &&
  a.exported == b.exported && sameList sameParameter a.params b.params &&
  a.constructorName.spelling == b.constructorName.spelling && map (\(_, name) => name.spelling) a.eliminator == map (\(_, name) => name.spelling) b.eliminator &&
  sameList sameField a.fields b.fields && sameList sameProjection a.projections b.projections
sameAuthored (InterfaceItem a) (InterfaceItem b) = a.name.spelling == b.name.spelling && a.level == b.level &&
  a.exported == b.exported && sameList sameParameter a.params b.params &&
  a.constructorName.spelling == b.constructorName.spelling && map (\(_, name) => name.spelling) a.eliminator == map (\(_, name) => name.spelling) b.eliminator &&
  sameList sameField a.fields b.fields && sameList sameProjection a.projections b.projections
sameAuthored _ _ = False

sameBody : DocumentBody -> DocumentBody -> Bool
sameBody EmptyDocument EmptyDocument = True
sameBody (ExpressionDocument a) (ExpressionDocument b) = sameExpr a b
sameBody (DeclarationDocument a) (DeclarationDocument b) = sameList sameAuthored a b
sameBody _ _ = False

public export
sameDocumentShape : ParsedDocument -> ParsedDocument -> Bool
sameDocumentShape a b = map (\header => header.components) a.moduleHeader == map (\header => header.components) b.moduleHeader &&
  map (\dependency => dependency.components) a.imports == map (\dependency => dependency.components) b.imports &&
  sameBody a.body b.body
