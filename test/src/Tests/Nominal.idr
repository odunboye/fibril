-- Closed non-recursive identity kernel; not a source declaration registry.
module Tests.Nominal

import Data.Fin
import Data.List
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Elaboration.Expression.Scope

%default total

accepts : Either error result -> Bool
accepts (Right _) = True
accepts _ = False

closed : Term 0 -> Term n
closed = rename absurd

shape : Term n
shape = VariantType [Nothing, Just (Linear, StringType)]

tagged : String -> List (Term n) -> Term n
tagged key indices = NominalType key indices shape

value : Term n
value = NominalValue (tagged "Example.Optional" []) (VariantValue shape 1 (Just (StringValue "present")))

constant : Term n -> Term n -> Term n
constant ty result = Lambda Erased ty (weaken result)

recover : Term 0
recover = NominalCase (constant (tagged "Example.Optional" []) StringType) value
  (Lambda Linear shape
    (VariantCase (constant shape StringType) (Variable FZ)
      [StringValue "missing", Lambda Linear StringType (Variable FZ)]))

typeShape : Term 0
typeShape = VariantType [Nothing, Just (Erased, Universe 0)]

typeTag : Term 0
typeTag = NominalType "Example.TypePacket" [] typeShape

family : Term 0
family = Lambda Erased typeTag
  (NominalCase (constant (closed typeTag) (Universe 0)) (Variable FZ)
    (Lambda Linear (closed typeShape)
      (VariantCase (constant (closed typeShape) (Universe 0)) (Variable FZ)
        [StringType, Lambda Erased (Universe 0) (Variable FZ)])))

identityMotive : Term 0
identityMotive = Lambda Erased typeTag
  (Pi Linear (Apply (closed family) (Variable FZ))
    (weaken (Apply (closed family) (Variable FZ))))

dependentIdentity : Term 0
dependentIdentity = NominalCase identityMotive
  (NominalValue typeTag (VariantValue typeShape 1 (Just StringType)))
  (Lambda Linear typeShape
    (VariantCase
      (Lambda Erased (closed typeShape)
        (Apply (closed identityMotive) (NominalValue (closed typeTag) (Variable FZ))))
      (Variable FZ)
      [Lambda Linear StringType (Variable FZ),
       Lambda Erased (Universe 0) (Lambda Linear (Variable FZ) (Variable FZ))]))

public export
checks : List (String, Bool)
checks =
  [ ("closed nominal type preserves its checked shape universe",
      case inferErased 512 128 Empty typeTag of Right (Universe 1) => True; _ => False)
  , ("nominal constructor and consuming elimination check",
      accepts (checkRuntime 512 128 Empty recover StringType))
  , ("nominal and variant elimination compose without hidden tag padding",
      case normalize 8 recover of Normal result => sameSyntax result (StringValue "present") && accepts (checkRuntime 512 128 Empty result StringType); _ => False)
  , ("different keys with equal shapes are distinct",
      not (accepts (checkRuntime 512 128 Empty value (tagged "Other.Optional" []))))
  , ("phantom parameters remain part of identity",
      not (accepts (checkRuntime 512 128 Empty
        (NominalValue (tagged "Example.Phantom" [StringType]) (VariantValue shape 0 Nothing))
        (tagged "Example.Phantom" [BoolType]))))
  , ("a key does not authorize a substituted shape witness",
      not (accepts (checkErased 512 128 Empty value
        (NominalType "Example.Optional" [] (VariantType [Nothing])))))
  , ("nominal values must check against the exact underlying shape",
      not (accepts (inferRuntime 512 128 Empty
        (NominalValue (tagged "Example.Optional" []) (VariantValue (VariantType [Nothing]) 0 Nothing)))))
  , ("malformed nominal shape and parameters are rejected",
      all (\ty => not (accepts (inferErased 512 128 Empty ty)))
        [NominalType "Bad" [] StringType,
         NominalType "Bad" [] (VariantType []),
         tagged "Bad" [Apply BoolTrue BoolFalse]])
  , ("beta-equivalent parameters give compatible identity",
      accepts (checkRuntime 512 128 Empty
        (NominalValue (tagged "Example.Phantom" [Apply (Lambda Erased (Universe 0) (Variable FZ)) StringType]) (VariantValue shape 0 Nothing))
        (tagged "Example.Phantom" [StringType])))
  , ("erased parameter information is not a runtime capture",
      let ty = tagged "Example.Indexed" [Variable FZ]
       in accepts (checkRuntime 512 128 (Extend Empty Erased BoolType)
         (NominalValue ty (VariantValue shape 0 Nothing)) ty))
  , ("retaining an index in a type does not discharge a linear runtime input",
      let ty = tagged "Example.Indexed" [Variable FZ]
       in not (accepts (checkRuntime 512 128 (Extend Empty Linear BoolType)
         (NominalValue ty (VariantValue shape 0 Nothing)) ty)))
  , ("dependent nominal case recovers identity at an erased carried type",
      accepts (checkRuntime 512 128 Empty (Apply dependentIdentity (StringValue "dependent")) StringType))
  , ("dependent nominal result reduces and independently rechecks",
      case normalize 64 (Apply dependentIdentity (StringValue "dependent")) of
        Normal result => sameSyntax result (StringValue "dependent") && accepts (checkRuntime 512 128 Empty result StringType)
        _ => False)
  , ("nominal case must consume its underlying variant once",
      not (accepts (checkRuntime 512 128 Empty
        (NominalCase (constant (tagged "Example.Optional" []) StringType) value (Lambda Linear shape (StringValue "drop"))) StringType)))
  , ("nominal motives cannot inspect an erased wrapper at runtime",
      not (accepts (checkRuntime 512 128 (Extend Empty Erased (tagged "Example.Optional" []))
        (NominalCase (constant (tagged "Example.Optional" []) shape) (Variable FZ) (Lambda Linear shape (Variable FZ))) shape)))
  , ("nominal motive domain and permission must match",
      not (accepts (inferErased 512 128 Empty
        (NominalCase (constant (tagged "Other.Optional" []) shape) value (Lambda Linear shape (Variable FZ))))))
  , ("nominal elimination is one contraction to application",
      case step recover of Just (Apply _ _) => True; _ => False)
  , ("nominal parameter cells count in size admission",
      typeNodes (the (Term 0) (tagged "Example.Phantom" [StringType])) == 7 &&
      typeNodes (the (Term 0) (tagged "Example.Phantom" (replicate 600 StringType))) == 513)
  , ("partial scope transport retains phantom parameter dependencies",
      case dropNewest (tagged "Example.Phantom" [the (Term 1) (Variable FZ)]) of Nothing => True; _ => False)
  , ("nominal parameter traversal reports checking exhaustion",
      not (accepts (inferErased 16 128 Empty (tagged "Example.Phantom" (replicate 32 StringType)))))
  ]
