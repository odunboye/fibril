module Tests.Box

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead

%default total

accepts : Either error value -> Bool
accepts (Right _) = True
accepts _ = False

tagType : Term 0
tagType = BoxType Erased (Universe 0)

tagOf : Term 0
tagOf = Lambda Erased tagType
  (BoxCase (Lambda Erased (weaken tagType) (Universe 0)) (Variable FZ)
    (Lambda Erased (Universe 0) (Variable FZ)))

identityMotive : Term 0
identityMotive = Lambda Erased tagType
  (Pi Linear (Apply (weaken tagOf) (Variable FZ))
             (weaken (Apply (weaken tagOf) (Variable FZ))))

dependentIdentity : Term 0
dependentIdentity = BoxCase identityMotive (BoxValue tagType StringType)
  (Lambda Erased (Universe 0) (Lambda Linear (Variable FZ) (Variable FZ)))

recover : Quantity -> Term 0
recover q = BoxCase (Lambda Erased (BoxType q BoolType) BoolType)
  (BoxValue (BoxType q BoolType) BoolTrue) (Lambda q BoolType (Variable FZ))

public export
checks : List (String, Bool)
checks =
  [ ("box formation preserves the domain universe",
      case inferErased 256 128 Empty tagType of Right (Universe 1) => True; _ => False)
  , ("dependent unary elimination constructs an identity at the wrapped type",
      accepts (checkRuntime 256 128 Empty (Apply dependentIdentity (StringValue "dependent")) StringType))
  , ("unary elimination reduces and rechecks without padding or eta",
      case normalize 3 (Apply dependentIdentity (StringValue "dependent")) of
        Normal result => sameSyntax result (StringValue "dependent") &&
                         accepts (checkRuntime 256 128 Empty result StringType)
        _ => False)
  , ("unary elimination reports insufficient head fuel",
      case weakHead 2 (Apply dependentIdentity (StringValue "dependent")) of HeadLimit _ => True; _ => False)
  , ("linear and unrestricted fields can be returned once",
      all (\q => accepts (checkRuntime 256 128 Empty (recover q) BoolType)) [Linear, Unrestricted])
  , ("unrestricted wrapped fields can be duplicated",
      let ty = BoxType Unrestricted BoolType
          branch = Lambda Unrestricted BoolType (BoolCase (Variable FZ) (Variable FZ) BoolFalse)
       in accepts (checkRuntime 256 128 Empty
         (BoxCase (Lambda Erased ty BoolType) (BoxValue ty BoolTrue) branch) BoolType))
  , ("erased fields remain available only to erased checking",
      accepts (checkErased 256 128 Empty (recover Erased) BoolType) &&
      not (accepts (checkRuntime 256 128 Empty (recover Erased) BoolType)))
  , ("linear wrapper fields cannot be dropped",
      let ty = BoxType Linear BoolType
       in not (accepts (checkRuntime 256 128 Empty
         (BoxCase (Lambda Erased ty BoolType) (BoxValue ty BoolTrue) (Lambda Linear BoolType BoolFalse)) BoolType)))
  , ("linear wrapper fields cannot be duplicated",
      let ty = BoxType Linear BoolType
          branch = Lambda Linear BoolType (BoolCase (Variable FZ) (Variable FZ) BoolFalse)
       in not (accepts (checkRuntime 256 128 Empty
         (BoxCase (Lambda Erased ty BoolType) (BoxValue ty BoolTrue) branch) BoolType)))
  , ("branch quantities must match the wrapper",
      not (accepts (checkErased 256 128 Empty
        (BoxCase (Lambda Erased (BoxType Linear BoolType) BoolType)
          (BoxValue (BoxType Linear BoolType) BoolTrue) (Lambda Unrestricted BoolType (Variable FZ))) BoolType)))
  , ("unrestricted fields cannot capture a linear ambient value",
      not (accepts (checkRuntime 256 128 (Extend Empty Linear StringType)
        (BoxValue (BoxType Unrestricted StringType) (Variable FZ)) (BoxType Unrestricted StringType))))
  , ("erased fields add no runtime capture demand",
      accepts (checkRuntime 256 128 (Extend Empty Erased StringType)
        (BoxValue (BoxType Erased StringType) (Variable FZ)) (BoxType Erased StringType)))
  , ("branch ambient captures count once and survive reduction",
      let ty = BoxType Erased UnitType
          branch = Lambda Erased UnitType (Variable (FS FZ))
          term = BoxCase (Lambda Erased ty StringType) (BoxValue ty UnitValue) branch
          context = Extend Empty Linear StringType
       in accepts (checkRuntime 256 128 context term StringType) &&
          case normalize 2 term of
            Normal result => sameSyntax result (Variable FZ) && accepts (checkRuntime 256 128 context result StringType)
            _ => False)
  , ("branch and scrutinee cannot share a linear capture",
      let ty = BoxType Linear StringType
          branch = Lambda Linear StringType (StringAppend (Variable FZ) (Variable (FS FZ)))
       in not (accepts (checkRuntime 256 128 (Extend Empty Linear StringType)
         (BoxCase (Lambda Erased ty StringType) (BoxValue ty (Variable FZ)) branch) StringType)))
  , ("box domains must be types",
      not (accepts (inferErased 256 128 Empty (BoxType Linear BoolTrue))))
  , ("a box annotation must be a box type",
      not (accepts (inferErased 256 128 Empty (BoxValue BoolType BoolTrue))))
  , ("a box payload must inhabit its annotation domain",
      not (accepts (inferErased 256 128 Empty (BoxValue (BoxType Linear BoolType) UnitValue))))
  , ("a box is not its payload type",
      not (accepts (checkErased 256 128 Empty (BoxValue (BoxType Linear BoolType) BoolTrue) BoolType)))
  , ("box quantities are invariant",
      not (accepts (checkErased 256 128 Empty (BoxValue (BoxType Linear BoolType) BoolTrue) (BoxType Unrestricted BoolType))))
  , ("box types are not runtime type data",
      not (accepts (checkRuntime 256 128 Empty (BoxType Linear BoolType) (Universe 0))))
  , ("box motive domain must match",
      not (accepts (inferErased 256 128 Empty
        (BoxCase (Lambda Erased UnitType BoolType) (BoxValue (BoxType Linear BoolType) BoolTrue)
          (Lambda Linear BoolType (Variable FZ))))))
  , ("box motives must return types",
      not (accepts (inferErased 256 128 Empty
        (BoxCase (Lambda Erased (BoxType Linear BoolType) BoolTrue) (BoxValue (BoxType Linear BoolType) BoolTrue)
          (Lambda Linear BoolType (Variable FZ))))))
  , ("box motive input must be erased",
      not (accepts (inferErased 256 128 Empty
        (BoxCase (Lambda Unrestricted (BoxType Linear BoolType) BoolType) (BoxValue (BoxType Linear BoolType) BoolTrue)
          (Lambda Linear BoolType (Variable FZ))))))
  ]
