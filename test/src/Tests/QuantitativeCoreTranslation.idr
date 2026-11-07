module Tests.QuantitativeCoreTranslation

import Data.Vect
import Fibril.Core.Quantity
import Fibril.Core.Usage

import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Quantitative.Usage
import Fibril.Core.Quantitative.CoreTranslation

%default total

compareChecks : {n : Nat} -> (context : Vect n Ty) -> (permissions, expected : Vect n Quantity) ->
  (ty : Ty) -> (term : Quantitative.Syntax.Term context ty) -> Annotations term -> Bool
compareChecks context permissions expected ty term ann =
  case (checkUsage permissions term,
        checkErased 100 100 (coreContext context permissions) (coreTerm ty term ann) (coreType ty),
        checkRuntime 100 100 (coreContext context permissions) (coreTerm ty term ann) (coreType ty)) of
    (Right (u ** _), Right (), Right result) => u == expected && result.usage == expected
    _ => False

openTerm : Quantitative.Syntax.Term [UnitTy, BoolTy] UnitTy
openTerm = If (Ref (There Here)) (UnitElim (Ref Here) Unit) (Ref Here)

hiddenInvalid : Quantitative.Syntax.Term [] UnitTy
hiddenInvalid = App (Lam Erased Unit) (Lam Linear Unit)

export
checks : List (String, Bool)
checks =
  [ ("translation: newest-first open context and joined branches",
      compareChecks [UnitTy, BoolTy] [Linear, Linear] [Linear, Linear] UnitTy openTerm
        (AIf (ARef) (AUnitElim ARef AUnit) ARef))
  , ("translation: nested lambdas retain quantities and scoping",
      compareChecks [] [] [] (Arrow Linear UnitTy (Arrow Linear BoolTy UnitTy))
        (Lam Linear (Lam Linear (If (Ref Here) (Ref (There Here)) (Ref (There Here)))))
        (ALam (ALam (AIf ARef ARef ARef))))
  , ("translation: application and unit elimination",
      compareChecks [] [] [] UnitTy (UnitElim (App (Lam Linear (Ref Here)) Unit) Unit)
        (AUnitElim (AApp UnitTy (ALam ARef) AUnit) AUnit))
  , ("translation: erased argument mismatch is explicit",
      case (inferUsage hiddenInvalid,
            checkRuntime 100 100 (coreContext [] [])
              (coreTerm UnitTy hiddenInvalid (AApp (Arrow Linear UnitTy UnitTy) (ALam AUnit) (ALam AUnit)))
              (coreType UnitTy)) of
        (Left _, Right result) => result.usage == []
        _ => False)
  ]
