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
import Fibril.Core.Renaming
import Fibril.Core.Substitution
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
  [ ("String lives in Type0",
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
