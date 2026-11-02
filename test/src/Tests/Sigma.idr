module Tests.Sigma

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Pretty

%default total

family : Term 0
family = Sigma Linear Linear BoolType (BoolCase (Variable FZ) StringType BoolType)

packageType : Term 0
packageType = Sigma Erased Linear (Universe 0) (Variable FZ)

accepts : Either error value -> Bool
accepts (Right _) = True
accepts _ = False

public export
checks : List (String, Bool)
checks =
  [ ("dependent pair formation uses the maximum universe",
      case inferErased 128 128 Empty packageType of
        Right (Universe 1) => True
        _ => False)
  , ("the second field depends on the actual first field: String branch",
      accepts (checkRuntime 128 128 Empty (PairValue family BoolTrue (StringValue "yes")) family))
  , ("the second field depends on the actual first field: Bool branch",
      accepts (checkRuntime 128 128 Empty (PairValue family BoolFalse BoolTrue) family))
  , ("dependent field mismatch is rejected",
      not (accepts (checkErased 128 128 Empty (PairValue family BoolFalse (StringValue "wrong")) family)))
  , ("a packaged erased type is not traversed as runtime data",
      accepts (checkRuntime 128 128 Empty (PairValue packageType StringType (StringValue "payload")) packageType))
  , ("a package value must inhabit its supplied type",
      not (accepts (checkErased 128 128 Empty (PairValue packageType BoolType (StringValue "wrong")) packageType)))
  , ("pair annotations must be pair types",
      case inferErased 128 128 Empty (PairValue StringType BoolTrue BoolFalse) of
        Left (ExpectedPairType _) => True
        _ => False)
  , ("Sigma is not runtime type data",
      not (accepts (checkRuntime 128 128 Empty family (Universe 0))))
  , ("two linear fields cannot duplicate a linear ambient variable",
      let ty = Sigma Linear Linear StringType StringType
       in not (accepts (checkRuntime 128 128 (Extend Empty Linear StringType)
                    (PairValue ty (Variable FZ) (Variable FZ)) ty)))
  , ("an unrestricted field scales ambient usage",
      let ty = Sigma Unrestricted Erased StringType UnitType
       in not (accepts (checkRuntime 128 128 (Extend Empty Linear StringType)
                    (PairValue ty (Variable FZ) UnitValue) ty)))
  , ("erased fields do not add runtime capture usage",
      let ty = Sigma Erased Linear StringType StringType
       in accepts (checkRuntime 128 128 (Extend Empty Linear StringType)
                    (PairValue ty (Variable FZ) (Variable FZ)) ty))
  , ("erased field values are still typechecked",
      let ty = Sigma Erased Linear BoolType StringType
       in not (accepts (checkRuntime 128 128 Empty
                    (PairValue ty (StringValue "wrong") (StringValue "value")) ty)))
  , ("quantities remain invariant under conversion",
      not (accepts (checkErased 128 128 Empty
        (PairValue (Sigma Linear Linear BoolType BoolType) BoolTrue BoolFalse)
        (Sigma Unrestricted Linear BoolType BoolType))))
  , ("full reduction normalizes fields; head inspection does not",
      let ty : Term 0 = Sigma Linear Linear BoolType BoolType
          first = Apply (Lambda Linear BoolType (Variable FZ)) BoolTrue
          term = PairValue ty first BoolFalse
       in case (weakHead 0 term, normalize 1 term) of
            (HeadForm exposed, Normal reduced) => sameSyntax exposed term &&
              sameSyntax reduced (PairValue ty BoolTrue BoolFalse)
            _ => False)
  , ("pair pretty printing exposes annotation and fields",
      renderTerm (PairValue packageType StringType (StringValue "payload")) ==
        "(Pair (Sigma 0 1 Type0 v0) String \"payload\")")
  ]
