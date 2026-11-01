module Tests.String

import Data.List
import Data.Vect
import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Usage
import Fibril.Core.Pretty
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Renaming
import Fibril.Core.Substitution
import Fibril.Source.Global
import Fibril.Source.Primitive
import Fibril.Driver.Check
import Fibril.Driver.Evaluate

%default total

accepted : Bool -> String -> Bool
accepted erased source = case checkSource erased source of
  Right _ => True
  Left _ => False

public export
checks : List (String, Bool)
checks =
  [ ("string append library name is not primitive",
      case lookupGlobal "appendString" primitiveGlobals of Nothing => True; _ => False)
  , ("string append library name can be shadowed",
      case evaluateSource 4 "let (1 appendString : Bool) = True in appendString" of
        Right lines => elem "Normal: True" lines
        _ => False)
  , ("string append primitive computes at one fuel",
      case normalize 1 (StringAppend (StringValue {n = 0} "λ ") (StringValue "🌍")) of
        Normal (StringValue value) => value == "λ 🌍"
        _ => False)
  , ("string append zero fuel cannot accept a normal form",
      case normalize 0 (StringAppend (StringValue {n = 0} "a") (StringValue "b")) of
        OutOfFuel _ => True
        _ => False)
  , ("string append head computation forces both operands",
      case weakHead 3 (StringAppend
        (Apply (Lambda Linear StringType (Variable FZ)) (StringValue {n = 0} "a"))
        (Apply (Lambda Linear StringType (Variable FZ)) (StringValue "b"))) of
        HeadForm (StringValue value) => value == "ab"
        _ => False)
  , ("string append operands require String",
      not (accepted False "appendString True \"text\"") &&
      not (accepted True "appendString \"text\" ()"))
  , ("string append library function is ordinary source",
      accepted False "\\(1 x : String) => appendString x \"suffix\"")
  , ("string append combines independent linear uses",
      case inferRuntime 30 30
        (Extend (Extend Empty Linear StringType) Linear StringType)
        (StringAppend (Variable (FS FZ)) (Variable FZ)) of
        Right result => result.usage == [Linear, Linear]
        _ => False)
  , ("string append rejects duplicated linear input before evaluation",
      not (accepted False "(\\(1 x : String) => appendString x x) \"linear\""))
  , ("string append rejects erased extraction",
      not (accepted False "(\\(0 x : String) => appendString x \"suffix\") \"erased\""))
  , ("string append exact empty result",
      case evaluateSource 128 "appendString \"\" \"\"" of
        Right lines => elem "Normal: \"\"" lines
        _ => False)
  , ("string append preserves decomposed Unicode",
      case normalize 1 (StringAppend (StringValue {n = 0} "e") (StringValue (pack [chr 0x301]))) of
        Normal value => sameSyntax value (StringValue ("e" ++ pack [chr 0x301])) &&
                        not (sameSyntax value (StringValue "é"))
        _ => False)
  , ("string append conversion spends a contraction",
      case betaCompare 1 (StringAppend (StringValue {n = 0} "a") (StringValue "b")) (StringValue "ab") of
        EqualNormalForms => True
        _ => False)
  , ("String lives in Type0",
      case inferErased 20 20 Empty StringType of
        Right ty => sameSyntax ty (Universe 0)
        Left _ => False)
  , ("string literal has String type and zero use",
      case inferRuntime 20 20 Empty (StringValue "hello") of
        Right result => sameSyntax result.inferredType StringType && result.usage == []
        Left _ => False)
  , ("String is not runtime type data", not (accepted False "String"))
  , ("String is valid erased type data", accepted True "(String : Type 0)")
  , ("string literal is ordinary source data", accepted False "\"hello\"")
  , ("string literal not function", not (accepted False "\"hello\" ()"))
  , ("string ascription", accepted False "(\"hello\" : String)")
  , ("string mismatch is structured",
      case checkSourceDetailed False "(\"hello\" : Bool)" of
        Left (RuntimeFailure (TypingError (TypeMismatch actual expected))) =>
          sameSyntax actual StringType && sameSyntax expected BoolType
        _ => False)
  , ("string linear identity",
      accepted False "(\\(1 x : String) => x) \"hello\"")
  , ("string linear discard rejected",
      not (accepted False "\\(1 x : String) => \"constant\""))
  , ("string erased extraction rejected",
      not (accepted False "\\(0 x : String) => x"))
  , ("string literal cannot consume linear ambient input",
      case inferRuntime 20 20 (Extend Empty Linear StringType) (StringValue "hello") of
        Left (ContextUsage 0 Linear Erased) => True
        _ => False)
  , ("string conditional computation",
      case evaluateSource 1 "if False then \"first\" else \"second\"" of
        Right lines => elem "Type: String" lines && elem "Normal: \"second\"" lines
        Left _ => False)
  , ("string conditional linear discard rejected",
      not (accepted False "\\(1 x : String) => if True then x else \"constant\""))
  , ("string remains normal at zero fuel",
      case evaluateSource 0 "\"hello\"" of
        Right lines => elem "Normal: \"hello\"" lines
        Left _ => False)
  , ("string escaped and raw Unicode equality",
      case resolveSource "\"λ 🌍\\nquote: \\\"\"" of
        Right (StringValue value) => value == "λ 🌍\nquote: \""
        _ => False)
  , ("string equality is literal data equality",
      case betaCompare 0 (StringValue {n = 0} "same") (StringValue "same") of
        EqualNormalForms => True
        _ => False)
  , ("string unequal literals remain different",
      case betaCompare 0 (StringValue {n = 0} "a") (StringValue "b") of
        DifferentNormalForms => True
        _ => False)
  , ("string normalization does not normalize Unicode",
      not (sameSyntax (StringValue {n = 0} "é") (StringValue ("e" ++ pack [chr 0x301]))))
  , ("string is not definitionally Unit",
      not (sameSyntax (StringValue {n = 0} "") UnitValue))
  , ("string rendering escapes control data",
      renderTerm (StringValue {n = 0} "hello\n") == "\"hello\\n\"")
  , ("string identity renaming theorem instantiated",
      case renameIdentity (StringValue {n = 2} "data") of
        Refl => True)
  , ("string identity substitution theorem instantiated",
      case substituteIdentity (StringValue {n = 2} "data") of
        Refl => True)
  ]
