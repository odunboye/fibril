-- The closed declaration API, not source data syntax or trusted schema typing.
module Tests.DataDeclaration

import Data.Fin
import Data.List
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.Size
import Fibril.Source.Global
import Fibril.Elaboration.Data

%default total

accepts : Either error result -> Bool
accepts (Right _) = True
accepts _ = False

optional : DataSpec 1
optional = DataInput ["Example"] "Optional" 0 (Extend Empty Erased (Universe 0))
  [Nothing, Just (Linear, Variable FZ)] ["Nothing", "Just"]

bindings : DataBundle -> List String
bindings bundle = bundle.typeDefinition.name :: map name bundle.constructorDefinitions

public export
checks : List (String, Bool)
checks =
  [ ("data keys use validated qualified identifiers",
      case dataKey ["Example", "Types"] "Optional" of Right key => key == "Example.Types.Optional"; _ => False)
  , ("invalid or anonymous data identities are rejected",
      all (\parts => not (accepts (dataKey parts "Optional"))) [[], ["Bad.Name"], ["Bad "], ["module"], ["_"]])
  , ("declaration construction has an exact preflight and cumulative remainder",
      case buildData (dataConstructionCost optional) [] optional of
        Right bundle => bundle.remainingNodes == 0 && bundle.layout.name == "Example.Optional" &&
          bundle.layout.parameterCount == 1 && map index bundle.layout.constructors == [0, 1] &&
          map payloadQuantity bundle.layout.constructors == [Nothing, Just Linear]
        _ => False)
  , ("one node below data construction estimate is rejected",
      not (accepts (buildData (minus (dataConstructionCost optional) 1) [] optional)))
  , ("generated data constructors independently recheck at their signatures",
      case buildData 200000 [] optional of
        Right bundle => all (\definition => accepts (checkRuntime 512 128 Empty definition.value definition.declaredType)) bundle.constructorDefinitions
        _ => False)
  , ("data type globals are erased and constructors are unrestricted non-providers",
      case buildData 200000 [] optional of
        Right bundle => bundle.typeDefinition.quantity == Erased &&
          all (\definition => definition.quantity == Unrestricted && definition.provider == Nothing) bundle.constructorDefinitions
        _ => False)
  , ("generated parameterized constructor builds a checked nominal value",
      case buildData 200000 [] optional of
        Right bundle => case (lookupGlobal "Example.Just" bundle.constructorDefinitions,
                              lookupGlobal "Example.Optional" [bundle.typeDefinition]) of
          (Just ctor, Just family) => accepts (checkRuntime 512 128 Empty
            (Apply (Apply ctor StringType) (StringValue "present")) (Apply family StringType))
          _ => False
        _ => False)
  , ("family use preserves the declared higher universe through an ascription",
      case buildData 200000 [] ({ level := 1 } optional) of
        Right bundle => case lookupGlobal "Example.Optional" [bundle.typeDefinition] of
          Just family => case inferErased 512 128 Empty (Apply family StringType) of Right (Universe 1) => True; _ => False
          _ => False
        _ => False)
  , ("erased type family occurrence does not become a runtime function",
      case buildData 200000 [] optional of
        Right bundle => case lookupGlobal "Example.Optional" [bundle.typeDefinition] of
          Just family => not (accepts (inferRuntime 512 128 Empty family))
          _ => False
        _ => False)
  , ("phantom data arguments survive generated family construction",
      let spec = DataInput ["Example"] "Flag" 0 (Extend Empty Erased (Universe 0)) [Nothing] ["MkFlag"]
       in case buildData 200000 [] spec of
         Right bundle => case (lookupGlobal "Example.MkFlag" bundle.constructorDefinitions, lookupGlobal "Example.Flag" [bundle.typeDefinition]) of
           (Just ctor, Just family) => not (accepts (checkRuntime 512 128 Empty (Apply ctor StringType) (Apply family BoolType)))
           _ => False
         _ => False)
  , ("dependent erased parameter order and values are preserved",
      let context = Extend (Extend Empty Erased (Universe 0)) Erased (Variable FZ)
          spec = DataInput ["Example"] "Witnessed" 0 context [Nothing] ["MkWitnessed"]
       in case buildData 200000 [] spec of
         Right bundle => case (lookupGlobal "Example.MkWitnessed" bundle.constructorDefinitions,
                               lookupGlobal "Example.Witnessed" [bundle.typeDefinition]) of
           (Just ctor, Just family) =>
             accepts (checkRuntime 512 128 Empty (Apply (Apply ctor StringType) (StringValue "a"))
               (Apply (Apply family StringType) (StringValue "a"))) &&
             not (accepts (checkRuntime 512 128 Empty (Apply (Apply ctor StringType) (StringValue "a"))
               (Apply (Apply family StringType) (StringValue "b"))))
           _ => False
         _ => False)
  , ("declarations reject duplicate or occupied qualified bindings",
      all (\spec => not (accepts (buildData 200000 [] spec)))
        (the (List (DataSpec 1)) [{ constructorNames := ["Just", "Just"] } optional,
         { constructorNames := ["Optional", "Just"] } optional,
         { constructorNames := ["_", "Just"] } optional]) &&
      not (accepts (buildData 200000 ["Example.Just"] optional)))
  , ("constructor count and nonempty shape must agree",
      not (accepts (buildData 200000 [] ({ constructorNames := ["Just"] } optional))) &&
      not (accepts (buildData 200000 [] (DataInput ["Example"] "Empty" 0 Empty [] []))))
  , ("data parameter permissions and payload kinds are checked",
      not (accepts (buildData 200000 [] ({ params := Extend Empty Unrestricted (Universe 0) } optional))) &&
      not (accepts (buildData 200000 [] (DataInput ["Example"] "Bad" 0 Empty [Just (Erased, BoolTrue)] ["MkBad"]))))
  , ("declared universe cannot hide a higher payload universe",
      not (accepts (buildData 200000 [] (DataInput ["Example"] "Small" 0 Empty [Just (Erased, Universe 0)] ["MkSmall"]))))
  , ("explicit direct and hidden self-key occurrences are rejected",
      let self = NominalType "Example.Loop" [] (VariantType [Nothing])
          hidden = Apply (Lambda Erased (Universe 0) StringType) self
       in all (\ty => not (accepts (buildData 200000 []
            (DataInput ["Example"] "Loop" 0 Empty [Just (Linear, ty)] ["MkLoop"])))) [self, hidden])
  , ("self detection is structural rather than a string substring search",
      accepts (buildData 200000 [] (DataInput ["Example"] "Text" 0 Empty
        [Just (Linear, NominalType "Other.Packet" [StringValue "Example.Text"] (VariantType [Nothing]))] ["MkText"])))
  , ("all payload quantities and a wider alternative list are supported",
      accepts (buildData 200000 [] (DataInput ["Example"] "Permissions" 0 Empty
        [Just (Erased, BoolType), Just (Linear, BoolType), Just (Unrestricted, BoolType), Nothing]
        ["Hide", "Once", "Many", "Absent"])))
  , ("packaged dependent fields can be a data payload",
      accepts (buildData 200000 [] (DataInput ["Example"] "Package" 1 Empty
        [Just (Linear, Sigma Erased Linear (Universe 0) (Variable FZ))] ["MkPackage"])))
  , ("wider data alternatives use resource admission rather than a fixed arity cap",
      accepts (buildData 200000 [] (DataInput ["Example"] "Wide" 0 Empty
        (replicate 16 Nothing) (map (\n => "Tag" ++ show n) (rangeFromTo 0 15)))))
  , ("malformed and self-referencing parameter domains are rejected",
      let own = NominalType "Example.BadParam" [] (VariantType [Nothing])
       in all (\domain => not (accepts (buildData 200000 [] (DataInput ["Example"] "BadParam" 0
             (Extend Empty Erased domain) [Nothing] ["MkBadParam"])))) [BoolTrue, own])
  , ("cumulative data construction admission is consumed across bundles",
      let second : DataSpec 1 = { name := "Other", constructorNames := ["Absent", "Present"] } optional
          amount = dataConstructionCost optional + dataConstructionCost second
       in case buildData amount [] optional of
         Right first => case buildData first.remainingNodes (bindings first) second of
           Right next => next.remainingNodes == 0 && not (accepts (buildData (minus first.remainingNodes 1) (bindings first) second))
           _ => False
         _ => False)
  ]
