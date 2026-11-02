module Tests.ConstructorPattern

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Source.Text
import Fibril.Source.Resolve.Error
import Fibril.Elaboration.Expression.Constructor

%default total

accepts : Either error value -> Bool
accepts (Right _) = True
accepts _ = False

boxed : Term 0
boxed = BoxType Linear StringType

packing : Term 0
packing = Lambda Linear StringType (BoxValue (weaken boxed) (Variable FZ))

branch : Term 0
branch = Lambda Linear StringType (Variable FZ)

public export
checks : List (String, Bool)
checks =
  [ ("named unary constructor checks against a fresh field",
      accepts (checkConstructor (At 0 1 1) 1 Empty packing branch))
  , ("a correctly typed but constant packer is not a constructor pattern",
      not (accepts (checkConstructor (At 0 1 1) 1 Empty
        (Lambda Linear StringType (BoxValue (weaken boxed) (StringValue "fixed"))) branch)))
  , ("constructor input quantities must match the fields",
      not (accepts (checkConstructor (At 0 1 1) 1 Empty
        (Lambda Unrestricted StringType (BoxValue (weaken boxed) (Variable FZ))) branch)))
  , ("a binary constructor must pack fields in authored order",
      let pair = Sigma Linear Linear StringType StringType
          swapped = Lambda Linear StringType (Lambda Linear StringType
            (PairValue (weaken (weaken pair)) (Variable FZ) (Variable (FS FZ))))
          fields = Lambda Linear StringType (Lambda Linear StringType (Variable FZ))
       in not (accepts (checkConstructor (At 0 1 1) 2 Empty swapped fields)))
  ]
