module Tests.UnitCase

import Data.Fin
import Data.List
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Erased
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
  [ ("unit case consumes linear input",
      accepted False "\\(1 x : Unit) => case x of () => ()")
  , ("unit case cannot consume erased input",
      not (accepted False "\\(0 x : Unit) => case x of () => ()"))
  , ("unit case cannot duplicate linear input",
      not (accepted False "\\(1 x : Unit) => case x of () => x"))
  , ("unit case supports independent branch type",
      accepted False "case () of () => \\(1 x : Unit) => x")
  , ("unit case rejects type scrutinee",
      not (accepted True "case Unit of () => ()"))
  , ("unit case rejects function scrutinee",
      not (accepted True "case (\\(1 x : Unit) => x) of () => ()"))
  , ("unit case only accepts empty pattern",
      not (accepted True "case () of (x) => ()"))
  , ("unit case nested syntax",
      accepted False "case case () of () => () of () => ()")
  , ("unit case beta and constructor computation",
      case evaluateSource 2 "(\\(1 x : Unit) => case x of () => ()) ()" of
        Right lines => elem "Normal: ()" lines
        Left _ => False)
  , ("unit case exhaustion explicit",
      case evaluateSource 0 "case () of () => ()" of
        Left _ => True
        Right _ => False)
  , ("unit case scrutinee reduces first",
      case step (UnitCase (Apply (Lambda Linear UnitType (Variable FZ)) UnitValue) (UnitValue {n = 0})) of
        Just result => sameSyntax result (UnitCase UnitValue UnitValue)
        Nothing => False)
  , ("unit case stuck branch normalizes under full reduction",
      case step (UnitCase (Variable {n = 1} FZ)
                         (Apply (Lambda Linear UnitType (Variable FZ)) UnitValue)) of
        Just result => sameSyntax result (UnitCase (Variable FZ) UnitValue)
        Nothing => False)
  , ("unit case weak head ignores stuck branch",
      case stepHead (UnitCase (Variable {n = 1} FZ)
                             (Apply (Lambda Linear UnitType (Variable FZ)) UnitValue)) of
        Nothing => True
        Just _ => False)
  , ("unit case weak head contracts constructor",
      case weakHead 1 (UnitCase UnitValue (UnitValue {n = 0})) of
        HeadForm result => sameSyntax result UnitValue
        _ => False)
  , ("unit case type reduction participates in compatibility",
      case checkErased 30 10 Empty UnitValue (UnitCase UnitValue UnitType) of
        Right () => True
        Left _ => False)
  , ("unit case comparison exhaustion not equality",
      case betaCompare 0 (UnitCase UnitValue (UnitValue {n = 0})) UnitValue of
        Inconclusive => True
        _ => False)
  ]
