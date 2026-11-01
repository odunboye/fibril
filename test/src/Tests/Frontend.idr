module Tests.Frontend

import Data.List
import Fibril.Core.Term
import Fibril.Core.Pretty
import Fibril.Driver.Check
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Parser
import Fibril.Source.Syntax

%default total

resolves : String -> String -> Bool
resolves source expected =
  case resolveSource source of
    Right term => renderTerm term == expected
    Left _ => False

fails : String -> Bool
fails source =
  case resolveSource source of
    Left _ => True
    Right _ => False

accepted : Bool -> String -> Bool
accepted mode source =
  case checkSource mode source of
    Right _ => True
    Left _ => False

||| Parser, lexical scope, and checker integration regression examples.
public export
checks : List (String, Bool)
checks =
  [ ("frontend universe", resolves "Type 2" "Type2")
  , ("frontend grouping", resolves "((Type 0))" "Type0")
  , ("frontend polymorphic identity",
      resolves "\\(0 A : Type 0) => \\(1 x : A) => x"
      "(Lam 0 Type0 (Lam 1 v0 v0))")
  , ("frontend Unicode alias",
      resolves "λ(0 A : Type 0) ⇒ λ(1 x : A) ⇒ x"
      "(Lam 0 Type0 (Lam 1 v0 v0))")
  , ("frontend dependent Pi", resolves "(0 A : Type 0) -> (1 x : A) -> A"
      "(Pi 0 Type0 (Pi 1 v0 v1))")
  , ("frontend arrow right associativity",
      resolves "Type 0 -> Type 1 -> Type 2"
      "(Pi unrestricted Type0 (Pi unrestricted Type1 Type2))")
  , ("frontend application left associativity",
      resolves "\\(f : Type 0) => f f f"
      "(Lam unrestricted Type0 ((v0 @ v0) @ v0))")
  , ("frontend anonymous arrow shifts result",
      resolves "\\(0 A : Type 0) => A -> A"
      "(Lam 0 Type0 (Pi unrestricted v0 v1))")
  , ("frontend shadowing/domain scope",
      resolves "\\(0 A : Type 0) => \\(1 A : A) => A"
      "(Lam 0 Type0 (Lam 1 v0 v0))")
  , ("frontend binder not in own domain", fails "\\(x : x) => x")
  , ("frontend unknown variable", fails "unknown")
  , ("frontend wildcard not referenceable", fails "\\(0 _ : Type 0) => _")
  , ("frontend missing close", fails "(Type 0")
  , ("frontend missing lambda body", fails "\\(1 x : Type 0) =>")
  , ("frontend invalid quantity", fails "\\(2 x : Type 0) => x")
  , ("frontend unsupported quantity spelling", fails "\\(01 x : Type 0) => x")
  , ("frontend missing universe level", fails "Type")
  , ("frontend numeric level bound", fails "Type 1234567")
  , ("frontend trailing token", fails "Type 0 )")
  , ("frontend valid runtime expression",
      accepted False "\\(0 A : Type 0) => \\(1 x : A) => x")
  , ("frontend erased universe", accepted True "Type 0")
  , ("frontend runtime universe rejected", not (accepted False "Type 0"))
  , ("frontend typed failure survives resolution", not (accepted True "Type 0 Type 0"))
  , ("frontend linear discard rejected",
      not (accepted False "\\(0 A : Type 0) => \\(1 x : A) => \\(1 y : A) => y"))
  , ("frontend erased discard allowed",
      accepted True "\\(0 A : Type 0) => \\(1 x : A) => \\(1 y : A) => y")
  , ("frontend parse budget explicit",
      case lexSource "Type 0" of
        Left _ => False
        Right tokens =>
          case parseExpression 0 (At 6 1 7) tokens of
            Left err => err.message == "Parser recursion budget exhausted"
            Right _ => False)
  , ("frontend EOF includes trailing newline",
      case resolveSource "Type\n" of
        Left (Parsing err) => err.position.line == 2 && err.position.column == 1
        _ => False)
  , ("frontend group extent",
      case lexSource "(Type 0)" of
        Left _ => False
        Right tokens =>
          case parseExpression 40 (At 8 1 9) tokens of
            Left _ => False
            Right expr => (extent expr).start.offset == 0 && (extent expr).finish.offset == 8)
  ]
