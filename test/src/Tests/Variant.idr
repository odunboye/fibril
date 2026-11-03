-- Kernel finite variants only; no source data declarations or recursive inductives.
module Tests.Variant

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
import Fibril.Driver.Console
import Fibril.Effect.Console

%default total

accepts : Either error result -> Bool
accepts (Right _) = True
accepts _ = False

flags : Term n
flags = VariantType [Nothing, Nothing]

constant : Term n -> Term n -> Term n
constant ty result = Lambda Erased ty (weaken result)

recover : Quantity -> Term 0
recover q =
  let ty = VariantType [Nothing, Just (q, BoolType)]
   in VariantCase (constant ty BoolType) (VariantValue ty 1 (Just BoolTrue))
        [BoolFalse, Lambda q BoolType (Variable FZ)]

tagType : Term 0
tagType = VariantType [Nothing, Just (Erased, Universe 0)]

tagOf : Term 0
tagOf = Lambda Erased tagType
  (VariantCase (constant (weaken tagType) (Universe 0)) (Variable FZ)
    [StringType, Lambda Erased (Universe 0) (Variable FZ)])

identityMotive : Term 0
identityMotive = Lambda Erased tagType
  (Pi Linear (Apply (weaken tagOf) (Variable FZ))
    (weaken (Apply (weaken tagOf) (Variable FZ))))

dependentIdentity : Term 0
dependentIdentity = VariantCase identityMotive (VariantValue tagType 1 (Just StringType))
  [Lambda Linear StringType (Variable FZ),
   Lambda Erased (Universe 0) (Lambda Linear (Variable FZ) (Variable FZ))]

public export
checks : List (String, Bool)
checks =
  [ ("variants reject empty alternative lists", not (accepts (inferErased 512 128 Empty (VariantType []))))
  , ("nullary alternatives form Type0", case inferErased 512 128 Empty (the (Term 0) flags) of Right (Universe 0) => True; _ => False)
  , ("variant universe is the maximum of payload universes",
      case inferErased 512 128 Empty (VariantType [Nothing, Just (Erased, Universe 1), Just (Linear, BoolType)]) of
        Right (Universe 2) => True; _ => False)
  , ("variant payload types are checked even when erased",
      not (accepts (inferErased 512 128 Empty (VariantType [Just (Erased, BoolTrue)]))))
  , ("variant field annotation is checked even when erased",
      not (accepts (inferRuntime 512 128 Empty (VariantValue tagType 1 (Just (StringValue "not a type"))))))
  , ("variant constructor tag and arity must match",
      all (\term => not (accepts (inferRuntime 512 128 Empty term)))
        [VariantValue flags 2 Nothing, VariantValue flags 0 (Just BoolTrue), VariantValue tagType 1 Nothing])
  , ("linear and unrestricted payloads can be recovered",
      all (\q => accepts (checkRuntime 512 128 Empty (recover q) BoolType)) [Linear, Unrestricted])
  , ("erased payload recovery remains erased-only",
      accepts (checkErased 512 128 Empty (recover Erased) BoolType) &&
      not (accepts (checkRuntime 512 128 Empty (recover Erased) BoolType)))
  , ("dependent motive computes an identity at a carried type",
      accepts (checkRuntime 512 128 Empty (Apply dependentIdentity (StringValue "dependent")) StringType))
  , ("dependent variant result reduces and independently rechecks",
      case normalize 32 (Apply dependentIdentity (StringValue "dependent")) of
        Normal value => sameSyntax value (StringValue "dependent") && accepts (checkRuntime 512 128 Empty value StringType)
        _ => False)
  , ("single nullary arm does not join its branch with zero demand",
      let ty = VariantType [Nothing]
          ctx = Extend Empty Linear StringType
       in accepts (checkRuntime 512 128 ctx
         (VariantCase (constant ty StringType) (VariantValue ty 0 Nothing) [Variable FZ]) StringType))
  , ("all alternatives can consume the same ambient linear input once",
      accepts (checkRuntime 512 128 (Extend Empty Linear StringType)
        (VariantCase (constant flags StringType) (VariantValue flags 0 Nothing) [Variable FZ, Variable FZ]) StringType))
  , ("known constructor does not excuse different linear branch demands",
      not (accepts (checkRuntime 512 128 (Extend Empty Linear StringType)
        (VariantCase (constant flags StringType) (VariantValue flags 0 Nothing) [Variable FZ, StringValue "drop"]) StringType)))
  , ("scrutinee and branch cannot share a linear capture",
      not (accepts (checkRuntime 512 128 (Extend Empty Linear flags)
        (VariantCase (constant flags flags) (Variable FZ) [Variable FZ, Variable FZ]) flags)))
  , ("an erased scrutinee tag cannot be inspected at runtime",
      not (accepts (checkRuntime 512 128 (Extend Empty Erased flags)
        (VariantCase (constant flags StringType) (Variable FZ) [StringValue "left", StringValue "right"]) StringType)))
  , ("unrestricted payload construction cannot capture a linear input",
      let ty = VariantType [Just (Unrestricted, StringType)]
       in not (accepts (checkRuntime 512 128 (Extend Empty Linear StringType)
         (VariantValue ty 0 (Just (Variable FZ))) ty)))
  , ("erased payload construction does not demand its ambient input",
      let ty = VariantType [Just (Erased, StringType)]
       in accepts (checkRuntime 512 128 (Extend Empty Erased StringType)
         (VariantValue ty 0 (Just (Variable FZ))) ty))
  , ("linear payload cannot be discarded",
      let ty = VariantType [Just (Linear, BoolType)]
       in not (accepts (checkRuntime 512 128 Empty
         (VariantCase (constant ty BoolType) (VariantValue ty 0 (Just BoolTrue))
           [Lambda Linear BoolType BoolFalse]) BoolType)))
  , ("linear payload cannot be duplicated",
      let ty = VariantType [Just (Linear, BoolType)]
       in not (accepts (checkRuntime 512 128 Empty
         (VariantCase (constant ty BoolType) (VariantValue ty 0 (Just BoolTrue))
           [Lambda Linear BoolType (BoolCase (Variable FZ) (Variable FZ) (Variable FZ))]) BoolType)))
  , ("unrestricted payload may be duplicated",
      let ty = VariantType [Just (Unrestricted, BoolType)]
       in accepts (checkRuntime 512 128 Empty
         (VariantCase (constant ty BoolType) (VariantValue ty 0 (Just BoolTrue))
           [Lambda Unrestricted BoolType (BoolCase (Variable FZ) (Variable FZ) (Variable FZ))]) BoolType))
  , ("original erased-global-shaped occurrence is rejected before tag reduction",
      let hidden = Apply (Lambda Erased flags (Variable FZ)) (VariantValue flags 0 Nothing)
          term = VariantCase (constant flags StringType) hidden [StringValue "left", StringValue "right"]
       in not (accepts (checkRuntime 512 128 Empty term StringType)))
  , ("variant quantities are conversion-invariant",
      not (accepts (checkErased 512 128 Empty
        (VariantValue (VariantType [Just (Linear, BoolType)]) 0 (Just BoolTrue))
        (VariantType [Just (Unrestricted, BoolType)]))))
  , ("unselected, missing and extra branches are still rejected",
      all (\branches => not (accepts (inferRuntime 512 128 Empty
        (VariantCase (constant flags StringType) (VariantValue flags 0 Nothing) branches))))
        [[StringValue "ok", BoolTrue], [StringValue "missing"], [StringValue "a", StringValue "b", StringValue "extra"]])
  , ("motive must have an erased matching domain and universe codomain",
      all (\motive => not (accepts (inferErased 512 128 Empty
        (VariantCase motive (VariantValue flags 0 Nothing) [StringValue "a", StringValue "b"]))))
        [Lambda Linear flags StringType, Lambda Erased BoolType StringType, Lambda Erased flags BoolTrue])
  , ("nullary elimination spends exactly one contraction",
      let term : Term 0 = VariantCase (constant flags StringType) (VariantValue flags 1 Nothing) [StringValue "a", StringValue "b"]
       in case (normalize 0 term, normalize 1 term, weakHead 1 term) of
         (OutOfFuel _, Normal value, HeadForm head) => sameSyntax value (StringValue "b") && sameSyntax head value
         _ => False)
  , ("payload elimination contracts to ordinary application",
      case step (recover Linear) of
        Just (Apply (Lambda Linear BoolType (Variable FZ)) BoolTrue) => True
        _ => False)
  , ("out-of-range raw tag reduction is total and stuck",
      let term : Term 0 = VariantCase (constant flags StringType) (VariantValue flags 99 Nothing) [StringValue "a", StringValue "b"]
       in case (step term, stepHead term) of (Nothing, Nothing) => True; _ => False)
  , ("neutral variant scrutinees do not select a branch",
      case stepHead (VariantCase (constant flags StringType) (the (Term 1) (Variable FZ)) [StringValue "a", StringValue "b"]) of Nothing => True; _ => False)
  , ("three and wider alternative lists are admitted without fixed arity caps",
      all (\count => let ty = VariantType (replicate count Nothing)
                      in accepts (checkRuntime 512 128 Empty
                        (VariantValue ty (minus count 1) Nothing) ty)) [3, 9, 16])
  , ("every tag in wider nullary cases selects and rechecks",
      all (\count => let ty = VariantType (replicate count Nothing)
                      in all (\tag => let term = VariantCase (constant ty StringType) (VariantValue ty tag Nothing)
                                                   (replicate count (StringValue "selected"))
                                       in accepts (checkRuntime 512 128 Empty term StringType) &&
                                          (case normalize 1 term of Normal value => sameSyntax value (StringValue "selected"); _ => False))
                           (rangeFromTo 0 (minus count 1))) [3, 9, 16])
  , ("erased variant IO payload is omitted from the pure output plan",
      let ty = VariantType [Just (Erased, IOType UnitType)]
          term = VariantCase (constant ty (IOType UnitType)) (VariantValue ty 0 (Just (WriteLine (StringValue "hidden"))))
                   [Lambda Erased (IOType UnitType) (IOPure UnitValue)]
       in case prepareIO 32 128 term of Right [] => True; _ => False)
  , ("unselected erased-use branch is rejected before IO planning",
      let ty = VariantType [Nothing, Just (Erased, IOType UnitType)]
          term = VariantCase (constant ty (IOType UnitType)) (VariantValue ty 0 Nothing)
                   [IOPure UnitValue, Lambda Erased (IOType UnitType) (Variable FZ)]
       in not (accepts (prepareIO 32 128 term)))
  , ("descriptor cells count toward bounded inference construction",
      typeNodes (the (Term 0) (VariantType (replicate 600 Nothing))) == 513 &&
      typeNodes (the (Term 0) (VariantType [Nothing, Just (Linear, StringType)])) == 4)
  , ("partial scope transport visits all payload types",
      case dropNewest (VariantType [Nothing, Just (Erased, the (Term 1) (Variable FZ))]) of Nothing => True; _ => False)
  , ("long alternative formation reports checking exhaustion",
      not (accepts (inferErased 16 128 Empty (VariantType (replicate 32 Nothing)))))
  ]
