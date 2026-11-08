module Tests.Cubical.CommonAdmission

import Data.Fin
import Data.Vect
import Fibril.Core.Quantity
import Fibril.Core.Usage
import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Quantitative.Usage
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Cubical.Logical.CommonAdmission
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

budget : AdmissionBudget
budget = MkAdmissionBudget 1000 100

accepted : Either AdmissionError a -> Bool
accepted (Right _) = True
accepted _ = False

mismatch : Either AdmissionError a -> Bool
mismatch (Left TypeMismatch) = True
mismatch _ = False

inputLimited : Either AdmissionError a -> Bool
inputLimited (Left InputLimit) = True
inputLimited _ = False

checkingLimited : Either AdmissionError a -> Bool
checkingLimited (Left CheckingLimit) = True
checkingLimited _ = False

-- Actual source usage, independent of admission and not an admission premise.
linearSource : Term [BoolTy] BoolTy
linearSource = App (Lam Linear (Ref Here)) (Ref Here)

linearUses : Uses Tests.Cubical.CommonAdmission.linearSource [Linear]
linearUses = UseApp (UseLam (UseRef Here) Refl) (UseRef Here)

linearRaw : AdmissionTerm 1
linearRaw = AApp LBool (ALam (AVar FZ)) (AVar FZ)

sourceImage : eraseAdmission Tests.Cubical.CommonAdmission.linearRaw =
  commonTerm (shadowTerm Tests.Cubical.CommonAdmission.linearSource)
sourceImage = Refl

-- Consumes the returned, accessible witness, not a manual target derivation.
linearRuns : Bool
linearRuns = case admitCommonTerm budget [LBool] linearRaw LBool of
  Left _ => False
  Right evidence => applyMorphism (higherOrderTermSemantics (termWitness evidence)) (True, ()) &&
    not (applyMorphism (higherOrderTermSemantics (termWitness evidence)) (False, ()))

-- A named path depending on BOTH the open ordinary environment and dimension.
openValue : Bool -> DM -> Bool
openValue b (side, other) = if side then not b else b

openPaths : carrier (commonDependentPathEnvironmentSetoid [LBool] [LBool])
openPaths = (MkCommonMorphism (\input => openValue (fst (fst input)) (snd input))
  (\{x}, {y}, rel => cong2 openValue (fst (fst rel)) (snd rel)), ())

openRaw : AdmissionPathTerm 1 1 1
openRaw = APAt FZ (Var FZ)

openRuns : Bool
openRuns = case admitCommonPathTerm budget [LBool] [LBool] 1 openRaw LBool of
  Left _ => False
  Right evidence =>
    let w = pathWitness evidence in
      not (applyMorphism (dependentPathSemantics w (\_ => (False, False))) ((False, ()), openPaths)) &&
      applyMorphism (dependentPathSemantics w (\_ => (True, True))) ((False, ()), openPaths) &&
      applyMorphism (dependentPathSemantics w (\_ => (False, False))) ((True, ()), openPaths) &&
      not (applyMorphism (dependentPathSemantics w (\_ => (True, True))) ((True, ()), openPaths)) &&
      -- Includes a nonvertex value and dimension substitution using the
      -- existing witness-mapping theorem, not automatic equality admission.
      applyMorphism (dependentPathSemantics w (\_ => (True, False))) ((False, ()), openPaths) &&
      (case mapHigherOrderPathDimensions (\_ => the (ScopedInterval 0) One) w of
        MkHigherOrderPathWitness ty mapped =>
          applyMorphism (dependentPathSemantics mapped absurd) ((False, ()), openPaths))

eliminatorsRun : Bool
eliminatorsRun =
  (case admitCommonTerm budget []
    (AUnitElim AUnit (AIf (ABool True) (ABool False) (ABool True))) LBool of
      Left _ => False
      Right evidence => not (applyMorphism (higherOrderTermSemantics (termWitness evidence)) ())) &&
  (case admitCommonPathTerm budget [] [] 0
    (APUnitElim (APOrdinary AUnit)
      (APApp LBool (APLam (APOrdinary (AVar FZ)))
        (APIf (APOrdinary (ABool True)) (APOrdinary (ABool False)) (APOrdinary (ABool True))))) LBool of
      Left _ => False
      Right evidence => not (applyMorphism (dependentPathSemantics (pathWitness evidence) absurd) ((), ())))

captureRuns : Bool
captureRuns = case admitCommonTerm budget [LBool] (ALam (AVar (FS FZ))) (LArrow LUnit LBool) of
  Left _ => False
  Right evidence => applyMorphism
    (applyMorphism (higherOrderTermSemantics (termWitness evidence)) (True, ())) ()

-- Under a new ordinary binder named paths must still see the OUTER variable.
pathCaptureRuns : Bool
pathCaptureRuns = case admitCommonPathTerm budget [LBool] [LBool] 1
  (APLam (APAt FZ (Var FZ))) (LArrow LBool LBool) of
  Left _ => False
  Right evidence => not (applyMorphism
    (applyMorphism (dependentPathSemantics (pathWitness evidence) (\_ => (False, False)))
      ((False, ()), openPaths)) True)

largeInterval : Nat -> ScopedInterval 1
largeInterval Z = Var FZ
largeInterval (S n) = Reverse (largeInterval n)

largeType : Nat -> LogicalType
largeType Z = LBool
largeType (S n) = LArrow LUnit (largeType n)

ordinaryIf : AdmissionTerm 0
ordinaryIf = AIf (ABool True) (ABool False) (ABool True)

pathIf : AdmissionPathTerm 0 0 0
pathIf = APIf (APOrdinary (ABool True)) (APOrdinary (ABool False)) (APOrdinary (ABool True))

-- Identical logical erasure does not distinguish source binder permissions.
quantitiesForgotten : commonTerm (shadowTerm (the (Term [] (Arrow Linear BoolTy BoolTy))
  (Lam Linear (Ref Here)))) = commonTerm (shadowTerm (the (Term [] (Arrow Erased BoolTy BoolTy))
  (Lam Erased (Ref Here))))
quantitiesForgotten = Refl

export
checks : List (String, Bool)
checks =
  [ ("CommonAdmission source linear application has independent Uses and executable admitted witness", linearRuns)
  , ("CommonAdmission open environment-dependent nonconstant path, both endpoints and dimension substitution", openRuns)
  , ("CommonAdmission ordinary and path eliminators have executable admitted witnesses", eliminatorsRun)
  , ("CommonAdmission ordinary binder retains outer variable", captureRuns)
  , ("CommonAdmission path binder does not capture outer path environment", pathCaptureRuns)
  , ("CommonAdmission rejects wrong ordinary result type", mismatch (admitCommonTerm budget [] (ABool True) LUnit))
  , ("CommonAdmission rejects wrong application domain annotation", mismatch
      (admitCommonTerm budget [] (AApp LUnit (ALam (AVar FZ)) (ABool True)) LBool))
  , ("CommonAdmission rejects wrong domain against typed function variable", mismatch
      (admitCommonTerm budget [LArrow LBool LBool] (AApp LUnit (AVar FZ) AUnit) LBool))
  , ("CommonAdmission rejects wrong ordinary index type", mismatch
      (admitCommonTerm budget [LUnit, LBool] (AVar FZ) LBool))
  , ("CommonAdmission checks nonzero ordinary index", accepted
      (admitCommonTerm budget [LUnit, LBool] (AVar (FS FZ)) LBool))
  , ("CommonAdmission rejects changed ordinary context", mismatch
      (admitCommonTerm budget [LUnit] (AVar FZ) LBool))
  , ("CommonAdmission rejects wrong named path index type", mismatch
      (admitCommonPathTerm budget [] [LUnit, LBool] 1 (APAt FZ (Var FZ)) LBool))
  , ("CommonAdmission checks nonzero named path index", accepted
      (admitCommonPathTerm budget [] [LUnit, LBool] 1 (APAt (FS FZ) (Var FZ)) LBool))
  , ("CommonAdmission rejects changed named context", mismatch
      (admitCommonPathTerm budget [LBool] [LUnit] 1 openRaw LBool))
  , ("CommonAdmission rejects nonfunction lambda expectation", mismatch
      (admitCommonTerm budget [] (ALam AUnit) LBool))
  , ("CommonAdmission checks ordinary if branches and unit elimination", accepted
      (admitCommonTerm budget [] (AUnitElim AUnit ordinaryIf) LBool))
  , ("CommonAdmission rejects mismatched if branch", mismatch
      (admitCommonTerm budget [] (AIf (ABool True) AUnit (ABool False)) LUnit))
  , ("CommonAdmission rejects nonunit elimination scrutinee", mismatch
      (admitCommonTerm budget [] (AUnitElim (ABool True) AUnit) LUnit))
  , ("CommonAdmission path application and unit elimination", accepted
      (admitCommonPathTerm budget [] [] 0
        (APUnitElim (APOrdinary AUnit)
          (APApp LBool (APLam (APOrdinary (AVar FZ))) pathIf)) LBool))
  , ("CommonAdmission rejects mismatched path application domain", mismatch
      (admitCommonPathTerm budget [] [] 0
        (APApp LUnit (APLam (APOrdinary (AVar FZ))) pathIf) LBool))
  , ("CommonAdmission sequential ordinary branch fuel exact boundary", checkingLimited
      (admitCommonTerm (MkAdmissionBudget 100 3) [] ordinaryIf LBool) && accepted
      (admitCommonTerm (MkAdmissionBudget 100 4) [] ordinaryIf LBool))
  , ("CommonAdmission sequential path and embedded ordinary fuel exact boundary", checkingLimited
      (admitCommonPathTerm (MkAdmissionBudget 100 6) [] [] 0 pathIf LBool) && accepted
      (admitCommonPathTerm (MkAdmissionBudget 100 7) [] [] 0 pathIf LBool))
  , ("CommonAdmission zero checking fuel fails closed", checkingLimited
      (admitCommonTerm (MkAdmissionBudget 100 0) [] AUnit LUnit))
  , ("CommonAdmission shared preflight exact boundary", inputLimited
      (admitCommonTerm (MkAdmissionBudget 2 1) [] (ABool True) LBool) && accepted
      (admitCommonTerm (MkAdmissionBudget 3 1) [] (ABool True) LBool))
  , ("CommonAdmission preflights large intervals before checking", inputLimited
      (admitCommonPathTerm (MkAdmissionBudget 30 0) [] [LBool] 1
        (APAt FZ (largeInterval 1000)) LBool))
  , ("CommonAdmission preflights context types before lookup", inputLimited
      (admitCommonTerm (MkAdmissionBudget 30 0) [largeType 1000] (AVar FZ) LBool))
  , ("CommonAdmission preflights ordinary context length", inputLimited
      (admitCommonTerm (MkAdmissionBudget 30 0) (replicate 1000 LBool) AUnit LUnit))
  , ("CommonAdmission preflights named context length", inputLimited
      (admitCommonPathTerm (MkAdmissionBudget 30 0) [] (replicate 1000 LBool) 0 (APOrdinary AUnit) LUnit))
  , ("CommonAdmission preflights expected type before type equality", inputLimited
      (admitCommonTerm (MkAdmissionBudget 30 0) [] AUnit (largeType 1000)))
  , ("CommonAdmission preflights annotations in all branches", inputLimited
      (admitCommonTerm (MkAdmissionBudget 30 0) []
        (AIf (ABool True) AUnit (AApp (largeType 1000) AUnit AUnit)) LUnit))
  , ("CommonAdmission preflights finite dimension scope", inputLimited
      (admitCommonPathTerm (MkAdmissionBudget 30 0) [] [] 1000 (APOrdinary AUnit) LUnit))
  , ("CommonAdmission constructive nested type comparison accepts equal types", case commonTypeDecEq
      (LArrow (LArrow LUnit LBool) LBool) (LArrow (LArrow LUnit LBool) LBool) of
        Yes Refl => True
        No _ => False)
  , ("CommonAdmission constructive nested type comparison distinguishes domains", case commonTypeDecEq
      (LArrow (LArrow LUnit LBool) LBool) (LArrow (LArrow LBool LBool) LBool) of
        No _ => True
        Yes _ => False)
  ]
