module Tests.Let

import Data.List
import Fibril.Driver.Check
import Fibril.Driver.Evaluate
import Fibril.Core.Term
import Fibril.Core.Pretty

%default total

accepted : Bool -> String -> Bool
accepted mode source =
  case checkSource mode source of
    Right _ => True
    Left _ => False

resolves : String -> String -> Bool
resolves source expected =
  case resolveSource source of
    Right term => renderTerm term == expected
    Left _ => False

||| Nonrecursive local bindings reuse existing typing and quantity checking.
public export
checks : List (String, Bool)
checks =
  [ ("let linear identity checked",
      accepted False "let (1 id : (1 x : Type 0) -> Type 0) = \\(1 x : Type 0) => x in id")
  , ("let unrestricted closed function checked",
      accepted False "let (id : (1 x : Type 0) -> Type 0) = \\(1 x : Type 0) => x in id")
  , ("let erased type supports dependent body",
      accepted False "let (0 A : Type 1) = Type 0 in \\(1 x : A) => x")
  , ("let erased value does not consume outer linear input",
      accepted False "\\(0 A : Type 0) => \\(1 x : A) => let (0 ignored : A) = x in x")
  , ("let erased extraction rejected",
      not (accepted False "\\(0 A : Type 0) => \\(1 x : A) => let (0 y : A) = x in y"))
  , ("let linear discard rejected",
      not (accepted False "\\(0 A : Type 0) => \\(1 x : A) => let (1 y : A) = x in x"))
  , ("let unrestricted argument rejects outer linear capture",
      not (accepted False "\\(0 A : Type 0) => \\(1 x : A) => let (y : A) = x in y"))
  , ("let annotation checked",
      not (accepted True "let (1 x : Type 0) = Type 0 in x"))
  , ("let value not recursively scoped",
      case resolveSource "let (1 x : Type 0) = x in x" of
        Left (Resolving _) => True
        _ => False)
  , ("let binder absent in annotation",
      case resolveSource "let (1 x : x) = Type 0 in x" of
        Left (Resolving _) => True
        _ => False)
  , ("let shadowing value sees outer binding",
      resolves "\\(0 A : Type 1) => let (0 A : Type 1) = A in A"
      "(Lam 0 Type1 ((Lam 0 Type1 v0) @ v0))")
  , ("let nested values associate correctly",
      accepted True "let (0 A : Type 2) = let (0 B : Type 1) = Type 0 in B in A")
  , ("let wildcard not referenceable",
      case resolveSource "let (0 _ : Type 1) = Type 0 in _" of
        Left (Resolving _) => True
        _ => False)
  , ("let missing equals rejected",
      not (accepted True "let (0 A : Type 1) Type 0 in A"))
  , ("let missing in rejected",
      not (accepted True "let (0 A : Type 1) = Type 0 A"))
  , ("let reference normalization",
      case evaluateSource 1 "let (0 A : Type 1) = Type 0 in \\(1 x : A) => x" of
        Right lines => elem "Normal: (Lam 1 Type0 v0)" lines
        Left _ => False)
  ]
