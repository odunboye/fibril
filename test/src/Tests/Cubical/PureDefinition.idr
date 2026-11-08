module Tests.Cubical.PureDefinition

import Data.Fin
import Data.Vect
import Data.Maybe
import Fibril.Core.Quantity
import Fibril.Core.Usage
import Fibril.Core.Term as C
import Fibril.Core.Quantitative.Syntax as Q
import Fibril.Core.Quantitative.CoreTranslation
import Fibril.Core.Quantitative.Usage
import Fibril.Cubical.Source.PureDefinition
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.CommonAdmission

%default total

-- These generic definitions typecheck only if the image retains exact source
-- syntax and the common typing judgment retains the actual context and type.
sourceReembeds : (raw : C.Term n) -> (image : PureImage ctx raw) ->
  coreTerm image.ty image.pureTerm image.annotations = raw
sourceReembeds raw image = image.exactSource

sourceCommonTyping : {0 ctx : Vect n Ty} -> (raw : C.Term n) -> (image : PureImage ctx raw) ->
  CommonHasType (shadowContext ctx)
    (eraseAdmission (pureAdmission image.pureTerm image.annotations)) (shadowType image.ty)
sourceCommonTyping raw image = pureAdmissionTyped image.pureTerm image.annotations

budget : AdmissionBudget
budget = MkAdmissionBudget 4096 1024

-- Execute admission's returned witness for an actual extracted production term.
conditionalRuns : Bool
conditionalRuns = case extractPure 64 [] (UnitCase UnitValue (BoolCase BoolTrue BoolFalse BoolTrue)) of
  Just (Image BoolTy term ann exact) => case admitCommonTerm budget [] (pureAdmission term ann) LBool of
    Right checked => not (applyMorphism (higherOrderTermSemantics checked.termWitness) ())
    _ => False
  _ => False

nonzeroVariableRuns : Bool
nonzeroVariableRuns = case extractPure 64 [UnitTy, BoolTy] (Variable (FS FZ)) of
  Just (Image BoolTy term ann exact) => case admitCommonTerm budget [LUnit, LBool] (pureAdmission term ann) LBool of
    Right checked => applyMorphism (higherOrderTermSemantics checked.termWitness) ((), (True, ())) &&
      not (applyMorphism (higherOrderTermSemantics checked.termWitness) ((), (False, ())))
    _ => False
  _ => False

captureRuns : Bool
captureRuns = case extractPure 64 [BoolTy] (Lambda Unrestricted UnitType (Variable (FS FZ))) of
  Just (Image (Arrow Unrestricted UnitTy BoolTy) term ann exact) =>
    case admitCommonTerm budget [LBool] (pureAdmission term ann) (LArrow LUnit LBool) of
      Right checked => applyMorphism (applyMorphism (higherOrderTermSemantics checked.termWitness) (True, ())) ()
      _ => False
  _ => False

applicationRuns : Bool
applicationRuns = case extractPure 64 [] (Apply (Lambda Linear BoolType (Variable FZ)) BoolTrue) of
  Just (Image BoolTy term ann exact) => case (pureUses term, admitCommonTerm budget [] (pureAdmission term ann) LBool) of
    (Just ([] ** uses), Right checked) => applyMorphism (higherOrderTermSemantics checked.termWitness) ()
    _ => False
  _ => False

linearIdentity : Q.Term [] (Arrow Linear BoolTy BoolTy)
linearIdentity = Lam Linear (Ref Here)

linearUsageRetained : Bool
linearUsageRetained = case pureUses Tests.Cubical.PureDefinition.linearIdentity of
  Just ([] ** UseLam (UseRef Here) permission) => True
  _ => False

public export
checks : List (String, Bool)
checks =
  [ ("PureDefinition: conditional and Unit elimination witness", conditionalRuns)
  , ("PureDefinition: nonzero variable preserves context/type", nonzeroVariableRuns)
  , ("PureDefinition: lambda preserves outer capture", captureRuns)
  , ("PureDefinition: application domain and returned witness", applicationRuns)
  , ("PureDefinition: actual linear Uses retained", linearUsageRetained)
  , ("PureDefinition: linear discard fails Uses", isNothing (pureUses (the (Q.Term [] (Arrow Linear BoolTy BoolTy)) (Lam Linear (Boolean True)))))
  , ("PureDefinition: linear duplication fails Uses", isNothing (pureUses (the (Q.Term [] (Arrow Linear BoolTy BoolTy)) (Lam Linear (If (Ref Here) (Ref Here) (Ref Here))))))
  , ("PureDefinition: application type mismatch fails", isNothing (extractPure 64 [] (Apply (Lambda Linear BoolType (Variable FZ)) UnitValue)))
  , ("PureDefinition: branches must have same type", isNothing (extractPure 64 [] (BoolCase BoolTrue UnitValue BoolFalse)))
  , ("PureDefinition: global references fail closed", isNothing (extractPure 64 [] (GlobalRef 0)))
  , ("PureDefinition: effects fail closed", isNothing (extractPure 64 [] (IOPure UnitValue)))
  , ("PureDefinition: naturals/recursors fail closed", isNothing (extractPure 64 [] NatZero))
  , ("PureDefinition: raw Fix cannot enter the pure fragment", isNothing (extractPure 64 [] (Fix (Pi Linear BoolType BoolType) (Lambda Linear BoolType (Apply (Variable (FS FZ)) (Variable FZ))))))
  , ("PureDefinition: resource references fail closed", isNothing (extractPure 64 [] (FileHandleValue 0 0)))
  , ("PureDefinition: erased lambda fails closed", isNothing (extractPure 64 [] (Lambda Erased BoolType BoolTrue)))
  , ("PureDefinition: dependent types fail closed", isNothing (readPureType 64 (the (C.Term 0) (Pi Linear (Universe 0) (Variable FZ)))))
  , ("PureDefinition: erased arrow fails closed", isNothing (readPureType 64 (the (C.Term 0) (Pi Erased BoolType BoolType))))
  , ("PureDefinition: extraction depth fails closed", isNothing (extractPure 1 [] (Lambda Linear BoolType (Variable FZ))))
  , ("PureDefinition: quantity difference cannot be erased by comparison", isNothing (samePureCore (the (C.Term 0) (Lambda Linear BoolType (Variable FZ))) (Lambda Unrestricted BoolType (Variable FZ))))
  , ("PureDefinition: no beta conversion", isNothing (samePureCore (the (C.Term 0) (Apply (Lambda Linear BoolType (Variable FZ)) BoolTrue)) BoolTrue))
  ]
