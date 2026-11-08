module Tests.DataCaseParser

import Data.List
import Fibril.Source.Document
import Fibril.Source.Lexer
import Fibril.Source.Syntax

%default total

parses : String -> Bool
parses source = case parseDocument 64 256 source of
  Right document => case document.body of ExpressionDocument (NDataCase _ _ _ _) => True; _ => False
  _ => False

many : Nat -> String
many count = "case x return p of\n" ++ concat (replicate count "  A => True\n")

inferred : String -> Bool
inferred source = case parseDocument 64 256 source of
  Right document => case document.body of ExpressionDocument (NDataCase _ _ Nothing _) => True; _ => False
  _ => False

recordCase : String -> Bool
recordCase source = case parseDocument 64 256 source of
  Right document => case document.body of
    ExpressionDocument (NConstructorCase _ _ _ _ _ _) => True
    -- A single inferred-field arm also carries a one-constructor data-case fallback.
    ExpressionDocument (NCaseEither _ (NConstructorCase _ _ _ _ _ _) (NDataCase _ _ Nothing [_])) => True
    _ => False
  _ => False

unitCase : String -> Bool
unitCase source = case parseDocument 64 256 source of
  Right document => case document.body of ExpressionDocument (NUnitCase _ _ _) => True; _ => False
  _ => False

public export
checks : List (String, Bool)
checks =
  [ ("data-case parser admits exactly 64 aligned branches", parses (many 64) && not (parses (many 65)))
  , ("data-case parser accepts a single nullary branch", parses (many 1))
  , ("data-case parser recognizes omitted motives", inferred "case x of\n  A => True\n  B value => value")
  , ("binary data patterns preserve both binders in source order",
      case parseDocument 64 256 "case xs of\n  Nil => x\n  Cons head tail => head" of
        Right document => case document.body of
          ExpressionDocument (NDataCase _ _ Nothing [(_, [], _), (_, [head, tail], _)]) =>
            head.spelling == "head" && tail.spelling == "tail"
          _ => False
        _ => False)
  , ("single unary pattern remains record syntax", recordCase "case x of\n  A value => value")
  , ("single binary pattern remains record syntax", recordCase "case x of\n  A left right => left")
  , ("unit case remains unit syntax", unitCase "case x of () => True")
  ]
