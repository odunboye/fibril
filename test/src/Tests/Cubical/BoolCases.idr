module Tests.Cubical.BoolCases

import Data.Fin
import Data.Vect
import Data.Maybe
import Fibril.Core.Quantity
import Fibril.Core.Term as C
import Fibril.Core.Reduction
import Fibril.Core.Quantitative.Syntax as Q
import Fibril.Core.Quantitative.CoreTranslation
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Source.PureDefinition
import Fibril.Cubical.Source.BoolCases

%default total

branched : BoolBody
branched = Conditional Input (Literal True) (Literal False)

identityAgreement : BoolAgreement Input Tests.Cubical.BoolCases.branched
identityAgreement = ByBoolCases Refl Refl

-- These generic declarations are machine-checked all-input theorems, not tests
-- that reinterpret two sample runs as a proof.
allInputs : (b : Bool) -> evaluateBody Input b = evaluateBody Tests.Cubical.BoolCases.branched b
allInputs = boolAgreementAll identityAgreement

bothActualFunctionsReduce : (q : Quantity) -> (b : Bool) ->
  (CoreSteps (the (C.Term 0) (Apply (Lambda q BoolType (Variable FZ)) (booleanCore b))) (booleanCore b),
   CoreSteps (the (C.Term 0) (Apply (Lambda q BoolType (BoolCase (Variable FZ) BoolTrue BoolFalse)) (booleanCore b))) (booleanCore b))
bothActualFunctionsReduce q b = boolAgreementOperational
  (UnaryBool q Input) (UnaryBool q Tests.Cubical.BoolCases.branched)
  (ALam ARef) (ALam (AIf ARef ABoolean ABoolean)) identityAgreement b

selectedSetoidRelation : (q : Quantity) ->
  morphismsRelated
    (applyMorphism (higherOrderTermSemantics (functionWitness (UnaryBool q Input))) ())
    (applyMorphism (higherOrderTermSemantics (functionWitness (UnaryBool q Tests.Cubical.BoolCases.branched))) ())
selectedSetoidRelation q = boolAgreementSetoid
  (UnaryBool q Input) (UnaryBool q Tests.Cubical.BoolCases.branched) identityAgreement

-- The operational theorem's argument is the original image and annotations.
actualImageReduces : {a : Ty} -> {raw : C.Term 0} ->
  (image : PureImage [] raw) -> (fun : BoolFunction image.pureTerm) -> (b : Bool) ->
  CoreSteps (Apply raw (booleanCore b)) (booleanCore (evaluateBody (functionBody fun) b))
actualImageReduces image fun b =
  rewrite sym image.exactSource in functionReduces fun image.annotations b

nested : BoolBody
nested = Conditional (Conditional Input (Literal False) (Literal True))
  (Literal False) (Literal True)

nestedAgreement : BoolAgreement Input Tests.Cubical.BoolCases.nested
nestedAgreement = ByBoolCases Refl Refl

sharedAllowance : Nat -> Bool
sharedAllowance fuel = case readBoolFunction fuel (Lam Linear (embedBody Input)) of
  Nothing => False
  Just (rest, left) => isJust (readBoolFunction rest (Lam Linear (embedBody Tests.Cubical.BoolCases.branched)))

referenceNormal : Bool -> Bool
referenceNormal b = case normalize 4
  (Apply (Lambda Linear BoolType (bodyCore Tests.Cubical.BoolCases.nested)) (booleanCore b)) of
    Normal result => isJust (samePureCore result (booleanCore b))
    _ => False

public export
checks : List (String, Bool)
checks =
  [ ("BoolCases: different syntax is not reflexivity", isNothing (samePureCore
      (the (C.Term 0) (Lambda Linear BoolType (bodyCore Input)))
      (Lambda Linear BoolType (bodyCore Tests.Cubical.BoolCases.branched))))
  , ("BoolCases: shared allowance exact success", sharedAllowance 5)
  , ("BoolCases: shared allowance exhaustion", not (sharedAllowance 4))
  , ("BoolCases: zero allowance rejects leaf", isNothing (readBoolBody 0 (embedBody Input)))
  , ("BoolCases: siblings share allowance", isNothing (readBoolBody 3 (embedBody Tests.Cubical.BoolCases.branched)))
  , ("BoolCases: nested reference reduction False", referenceNormal False)
  , ("BoolCases: nested reference reduction True", referenceNormal True)
  , ("BoolCases: erased function rejected", isNothing (readBoolFunction 20 (Lam Erased (embedBody Input))))
  , ("BoolCases: application wrapper rejected", isNothing (readBoolFunction 20
      (the (Q.Term [] (Arrow Linear BoolTy BoolTy)) (Lam Linear (App (Lam Linear (Ref Here)) (Ref Here))))))
  , ("BoolCases: Unit function rejected", isNothing (readBoolFunction 20
      (the (Q.Term [] (Arrow Linear UnitTy BoolTy)) (Lam Linear (Boolean True)))))
  , ("BoolCases: higher-order function rejected", isNothing (readBoolFunction 20
      (the (Q.Term [] (Arrow Linear BoolTy (Arrow Linear BoolTy BoolTy))) (Lam Linear (Lam Linear (Ref Here))))))
  ]
