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

-- A genuinely dependent motive: compute the payload type of a package.
-- Its internal extraction is erased computation; it is not runtime projection.
payloadType : Term 0
payloadType = Lambda Erased packageType
  (PairCase (Lambda Erased (weaken packageType) (Universe 0)) (Variable FZ)
    (Lambda Erased (Universe 0) (Lambda Linear (Variable FZ) (Variable (FS FZ)))))

payloadBranch : Term 0
payloadBranch = Lambda Erased (Universe 0) (Lambda Linear (Variable FZ) (Variable FZ))

payload : Term 0
payload = PairCase payloadType (PairValue packageType StringType (StringValue "payload")) payloadBranch

boolPair : Term 0
boolPair = Sigma Linear Linear BoolType BoolType

boolMotive : Term 0
boolMotive = Lambda Erased boolPair BoolType

boolBranch : Term 0
boolBranch = Lambda Linear BoolType (Lambda Linear BoolType
  (BoolCase (Variable (FS FZ)) (Variable FZ) (Variable FZ)))

accepts : Either error value -> Bool
accepts (Right _) = True
accepts _ = False

public export
checks : List (String, Bool)
checks =
  [ ("a dependent motive recovers a package payload type",
      accepts (checkRuntime 256 128 Empty payload StringType))
  , ("dependent elimination computes and rechecks",
      case normalize 3 payload of
        Normal result => sameSyntax result (StringValue "payload") &&
                         accepts (checkRuntime 256 128 Empty result StringType)
        _ => False)
  , ("pair elimination has explicit fuel exhaustion",
      case weakHead 2 payload of HeadLimit _ => True; _ => False)
  , ("linear elimination consumes both fields",
      accepts (checkRuntime 256 128 Empty
        (PairCase boolMotive (PairValue boolPair BoolTrue BoolFalse) boolBranch) BoolType))
  , ("dropping a linear field is rejected",
      let branch = Lambda Linear BoolType (Lambda Linear BoolType (Variable (FS FZ)))
       in not (accepts (checkRuntime 256 128 Empty
         (PairCase boolMotive (PairValue boolPair BoolTrue BoolFalse) branch) BoolType)))
  , ("duplicating a linear field is rejected",
      let branch = Lambda Linear BoolType (Lambda Linear BoolType
                     (BoolCase (Variable (FS FZ))
                       (BoolCase (Variable (FS FZ)) (Variable FZ) (Variable FZ)) (Variable FZ)))
       in not (accepts (checkRuntime 256 128 Empty
         (PairCase boolMotive (PairValue boolPair BoolTrue BoolFalse) branch) BoolType)))
  , ("branch quantities must match the Sigma",
      let branch = Lambda Unrestricted BoolType (Lambda Linear BoolType
                     (BoolCase (Variable (FS FZ)) (Variable FZ) (Variable FZ)))
       in not (accepts (checkErased 256 128 Empty
         (PairCase boolMotive (PairValue boolPair BoolTrue BoolFalse) branch) BoolType)))
  , ("erased fields cannot be extracted at runtime",
      let ty = Sigma Erased Linear BoolType UnitType
          motive = Lambda Erased ty BoolType
          branch = Lambda Erased BoolType (Lambda Linear UnitType
                     (UnitCase (Variable FZ) (Variable (FS FZ))))
       in accepts (checkErased 256 128 Empty (PairCase motive (PairValue ty BoolTrue UnitValue) branch) BoolType) &&
          not (accepts (checkRuntime 256 128 Empty (PairCase motive (PairValue ty BoolTrue UnitValue) branch) BoolType)))
  , ("an erased ambient record cannot be consumed at runtime",
      not (accepts (checkRuntime 256 128 (Extend Empty Erased boolPair)
        (PairCase (weaken boolMotive) (Variable FZ) (weaken boolBranch)) BoolType)))
  , ("motive domains must match the scrutinee",
      not (accepts (inferErased 256 128 Empty
        (PairCase (Lambda Erased UnitType BoolType) (PairValue boolPair BoolTrue BoolFalse) boolBranch))))
  , ("motives must return types",
      not (accepts (inferErased 256 128 Empty
        (PairCase (Lambda Erased boolPair BoolTrue) (PairValue boolPair BoolTrue BoolFalse) boolBranch))))
  , ("motive input is erased",
      not (accepts (inferErased 256 128 Empty
        (PairCase (Lambda Unrestricted boolPair BoolType) (PairValue boolPair BoolTrue BoolFalse) boolBranch))))
  , ("branch ambient captures are counted once and survive beta",
      let ty = Sigma Erased Erased UnitType UnitType
          motive = Lambda Erased ty StringType
          branch = Lambda Erased UnitType (Lambda Erased UnitType (Variable (FS (FS FZ))))
          term = PairCase motive (PairValue ty UnitValue UnitValue) branch
          context = Extend Empty Linear StringType
       in accepts (checkRuntime 256 128 context term StringType) &&
          case normalize 3 term of
            Normal result => sameSyntax result (Variable FZ) && accepts (checkRuntime 256 128 context result StringType)
            _ => False)
  , ("scrutinee and branch cannot share a linear capture",
      let ty = Sigma Linear Erased StringType UnitType
          motive = Lambda Erased ty StringType
          branch = Lambda Linear StringType (Lambda Erased UnitType
                     (StringAppend (Variable (FS FZ)) (Variable (FS (FS FZ)))))
          term = PairCase motive (PairValue ty (Variable FZ) UnitValue) branch
       in not (accepts (checkRuntime 256 128 (Extend Empty Linear StringType) term StringType)))
  , ("non-pair scrutinees reject",
      not (accepts (inferErased 256 128 Empty (PairCase boolMotive BoolTrue boolBranch))))
  , ("dependent pair formation uses the maximum universe",
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
