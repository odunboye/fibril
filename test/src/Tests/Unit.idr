module Tests.Unit

import Data.Fin
import Data.Vect
import Data.List
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Usage
import Fibril.Driver.Check
import Fibril.Driver.Evaluate

%default total

accepted : Bool -> String -> Bool
accepted erased source =
  case checkSource erased source of
    Right _ => True
    Left _ => False

public export
checks : List (String, Bool)
checks =
  [ ("Unit lives in Type0",
      case inferErased 10 10 Empty UnitType of
        Right ty => sameSyntax ty (Universe 0)
        Left _ => False)
  , ("unit has Unit type and zero usage",
      case inferRuntime 10 10 Empty UnitValue of
        Right result => sameSyntax result.inferredType UnitType && result.usage == []
        Left _ => False)
  , ("Unit cannot be runtime type value",
      case inferRuntime 10 10 Empty UnitType of
        Left RuntimeTypeExpression => True
        _ => False)
  , ("Unit literal does not silently consume linear ambient variable",
      case inferRuntime 10 10 (Extend Empty Linear UnitType) UnitValue of
        Left (ContextUsage 0 Linear Erased) => True
        _ => False)
  , ("unit is stable under substitution",
      sameSyntax (substituteTerm (\_ => UnitValue {n = 0}) (UnitValue {n = 1})) UnitValue)
  , ("Unit type stable under renaming",
      sameSyntax (weaken (UnitType {n = 0})) UnitType)
  , ("unit has no reduction step", case step (UnitValue {n = 0}) of
        Nothing => True
        _ => False)
  , ("Unit has head form at zero fuel", case weakHead 0 (UnitType {n = 0}) of
        HeadForm ty => sameSyntax ty UnitType
        _ => False)
  , ("no unit eta rule equates variable with constructor",
      case betaCompare 0 (Variable {n = 1} FZ) UnitValue of
        DifferentNormalForms => True
        _ => False)
  , ("Unit type distinct from universe and constructor",
      not (sameSyntax (UnitType {n = 0}) (Universe 0)) &&
      not (sameSyntax (UnitType {n = 0}) UnitValue))
  , ("unit value source", accepted False "()")
  , ("unit grouping whitespace", accepted False "(( ))")
  , ("unit ascription", accepted False "(() : Unit)")
  , ("Unit upward sort compatibility", accepted True "(Unit : Type 2)")
  , ("unit is not a type", not (accepted True "(() : Type 0)"))
  , ("unit is not a function", not (accepted False "() ()"))
  , ("unit identity application", accepted False "(\\(1 x : Unit) => x) ()")
  , ("unit linear discard remains rejected",
      not (accepted False "\\(1 x : Unit) => ()"))
  , ("unit erased discard allowed", accepted False "\\(0 x : Unit) => ()")
  , ("unit let value evaluates",
      case evaluateSource 1 "let (1 value : Unit) = () in value" of
        Right lines => elem "Normal: ()" lines && elem "Type: Unit" lines
        Left _ => False)
  , ("unit already normal at zero fuel",
      case evaluateSource 0 "()" of
        Right lines => elem "Normal: ()" lines
        Left _ => False)
  ]
