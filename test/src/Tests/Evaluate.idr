module Tests.Evaluate

import Data.List
import Fibril.Driver.Evaluate

%default total

redex : String
redex = "(\\(1 f : (1 x : Type 0) -> Type 0) => f) (\\(1 x : Type 0) => x)"

||| Checked source evaluation rejects invalid inputs before normalization.
public export
checks : List (String, Bool)
checks =
  [ ("eval ascription computes without changing normal identity",
      case evaluateSource 1
        "(\\(0 A : Type 0) => \\(1 x : A) => x : (0 A : Type 0) -> (1 x : A) -> A)" of
        Right lines => elem "Normal: (Lam 0 Type0 (Lam 1 v0 v0))" lines
        Left _ => False)
  , ("eval normalizes checked expression",
      case evaluateSource 1 redex of
        Right lines => elem "Normal: (Lam 1 Type0 v0)" lines
        Left _ => False)
  , ("eval exact fuel exhaustion explicit",
      case evaluateSource 0 redex of
        Left err => err == "Evaluation budget exhausted; no normal form reported"
        Right _ => False)
  , ("eval already-normal function needs zero fuel",
      case evaluateSource 0 "\\(0 A : Type 0) => \\(1 x : A) => x" of
        Right _ => True
        Left _ => False)
  , ("eval runtime types remain unsupported",
      case evaluateSource 10 "Type 0" of
        Left _ => True
        Right _ => False)
  , ("eval unbound source fails",
      case evaluateSource 10 "missing" of
        Left _ => True
        Right _ => False)
  , ("eval cannot hide invalid linear use",
      case evaluateSource 10 "\\(0 A : Type 0) => \\(1 x : A) => \\(1 y : A) => y" of
        Left _ => True
        Right _ => False)
  ]
