module Tests.Alternatives

import Data.List
import Data.Vect
import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Usage
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Runtime

%default total

quantities : List Quantity
quantities = [Erased, Linear, Unrestricted]

laws : Bool
laws = all (\a => all (\b => all (\c =>
    joinQuantity a a == a &&
    joinQuantity a b == joinQuantity b a &&
    joinQuantity a (joinQuantity b c) == joinQuantity (joinQuantity a b) c &&
    joinQuantity (add a b) (add a c) == add a (joinQuantity b c) &&
    joinQuantity (multiply a b) (multiply a c) == multiply a (joinQuantity b c) &&
    allows a (joinQuantity b c) == (allows a b && allows a c)
  ) quantities) quantities) quantities

public export
checks : List (String, Bool)
checks =
  [ ("alternative permission laws exhaust all coefficients", laws)
  , ("alternative join is not addition",
      joinQuantity Linear Linear == Linear && add Linear Linear == Unrestricted)
  , ("alternative unequal exact uses require unrestricted permission",
      joinQuantity Erased Linear == Unrestricted)
  , ("alternative vector join is pointwise",
      joinUsage [Erased, Linear, Unrestricted] [Linear, Linear, Erased] ==
        [Unrestricted, Linear, Unrestricted])
  , ("alternative linear context rejects branch discard",
      case inferRuntime 30 30 (Extend Empty Linear UnitType)
        (BoolCase BoolTrue (Variable FZ) UnitValue) of
        Left (ContextUsage 0 Linear Unrestricted) => True
        _ => False)
  , ("alternative erased context rejects possible extraction",
      case inferRuntime 30 30 (Extend Empty Erased UnitType)
        (BoolCase BoolFalse (Variable FZ) UnitValue) of
        Left (ContextUsage 0 Erased Unrestricted) => True
        _ => False)
  , ("alternative unrestricted context permits branch discrepancy",
      case inferRuntime 30 30 (Extend Empty Unrestricted UnitType)
        (BoolCase BoolTrue (Variable FZ) UnitValue) of
        Right result => result.usage == [Unrestricted]
        _ => False)
  , ("alternative linear context accepts shared once",
      case inferRuntime 30 30 (Extend Empty Linear UnitType)
        (BoolCase BoolTrue (Variable FZ) (Variable FZ)) of
        Right result => result.usage == [Linear]
        _ => False)
  ]
