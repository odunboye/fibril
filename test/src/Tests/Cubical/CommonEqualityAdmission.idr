module Tests.Cubical.CommonEqualityAdmission

import Data.Fin
import Data.Vect
import Fibril.Core.Quantity
import Fibril.Core.Usage
import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Quantitative.Usage
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.CommonAdmission
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

budget : AdmissionBudget
budget = MkAdmissionBudget 1000 100

accepted : Either AdmissionError a -> Bool
accepted (Right _) = True
accepted _ = False

syntaxMismatch : Either AdmissionError a -> Bool
syntaxMismatch (Left SyntaxMismatch) = True
syntaxMismatch _ = False

typeMismatch : Either AdmissionError a -> Bool
typeMismatch (Left TypeMismatch) = True
typeMismatch _ = False

inputLimited : Either AdmissionError a -> Bool
inputLimited (Left InputLimit) = True
inputLimited _ = False

checkingLimited : Either AdmissionError a -> Bool
checkingLimited (Left CheckingLimit) = True
checkingLimited _ = False

unsupported : Either AdmissionError a -> Bool
unsupported (Left UnsupportedEquality) = True
unsupported _ = False

-- Actual linear source If; the independent source judgment is never an input.
linearIf : Term [BoolTy] BoolTy
linearIf = If (Ref Here) (Boolean False) (Boolean True)

linearUses : Uses Tests.Cubical.CommonEqualityAdmission.linearIf [Linear]
linearUses = UseIf (UseRef Here) UseBoolean UseBoolean

linearRaw : AdmissionPathTerm 1 0 0
linearRaw = APIf (APOrdinary (AVar FZ)) (APOrdinary (ABool False)) (APOrdinary (ABool True))

sourceImage : eraseAdmissionPath Tests.Cubical.CommonEqualityAdmission.linearRaw =
  CPIf (CPOrdinary (CVar FZ)) (CPOrdinary (CBool False)) (CPOrdinary (CBool True))
sourceImage = Refl

ordinarySourceImage : eraseAdmission (AIf (AVar FZ) (ABool False) (ABool True)) =
  commonTerm (shadowTerm Tests.Cubical.CommonEqualityAdmission.linearIf)
ordinarySourceImage = Refl

sourceRaw : AdmissionPathTerm 1 0 0
sourceRaw = APOrdinary (AIf (AVar FZ) (ABool False) (ABool True))

exactSourceImage : eraseAdmissionPath Tests.Cubical.CommonEqualityAdmission.sourceRaw =
  CPOrdinary (commonTerm (shadowTerm Tests.Cubical.CommonEqualityAdmission.linearIf))
exactSourceImage = Refl

sourceReflRuns : Bool
sourceReflRuns = case admitCommonEquality budget [LBool] ADNil STop sourceRaw sourceRaw LBool AERefl of
  Left _ => False
  Right input => let w = pathWitness (equalityLeft (admittedEquality input)) in
    not (applyMorphism (dependentPathSemantics w absurd) ((True, ()), ())) &&
    applyMorphism (dependentPathSemantics w absurd) ((False, ()), ())

ifCert : AdmissionEquality n k d
ifCert = AEIf AERefl (AESym AERefl) AERefl

-- Execute both returned witnesses and consume automatically produced semantic
-- evidence through the authoritative soundness theorem, not manual equality.
boolEqualityObserved : {x, y : Bool} -> x = y -> Bool
boolEqualityObserved Refl = True

linearRuns : Bool
linearRuns = case admitCommonEquality budget [LBool] ADNil STop linearRaw linearRaw LBool ifCert of
  Left _ => False
  Right (MkAdmittedEqualityInput CheckedNoPaths e) =>
    let l = pathWitness (equalityLeft e)
        r = pathWitness (equalityRight e)
        sound = dependentEndpointFaceEvidenceSound (equalityEvidence e () DependentAdmissibleNil)
          (True, ()) absurd Refl
    in boolEqualityObserved sound &&
      not (applyMorphism (dependentPathSemantics l absurd) ((True, ()), ())) &&
      applyMorphism (dependentPathSemantics r absurd) ((False, ()), ())

unitRaw : AdmissionPathTerm 0 0 0
unitRaw = APUnitElim (APOrdinary AUnit) (APOrdinary (ABool True))

appRaw : AdmissionPathTerm 1 0 0
appRaw = APApp (LArrow LBool LBool)
  (APLam (APApp LBool (APOrdinary (AVar FZ)) (APOrdinary (AVar (FS FZ)))))
  (APLam (APOrdinary (AVar FZ)))

openDecls : AdmissionDeclarations 1 1
openDecls = ADCons LBool (AVar FZ) (AIf (AVar FZ) (ABool False) (ABool True)) ADNil

openRaw : AdmissionPathTerm 1 1 1
openRaw = APAt FZ (Var FZ)

openValue : Bool -> DM -> Bool
openValue b (side, other) = if side then not b else b

openPaths : carrier (commonDependentPathEnvironmentSetoid [LBool] [LBool])
openPaths = (MkCommonMorphism (\input => openValue (fst (fst input)) (snd input))
  (\{x}, {y}, rel => cong2 openValue (fst (fst rel)) (snd rel)), ())

-- Uniform provider instantiated with ACTUAL model assumptions. These premises
-- are about an interpretation of declarations, not caller target equality.
openSound : (input : AdmittedEqualityInput [LBool] Tests.Cubical.CommonEqualityAdmission.openDecls
    (the (ScopedFace 1) STop) Tests.Cubical.CommonEqualityAdmission.openRaw
    Tests.Cubical.CommonEqualityAdmission.openRaw LBool) ->
  (ps : carrier (commonDependentPathEnvironmentSetoid [LBool] [LBool])) ->
  (adm : DependentPathAdmissible (checkedDeclarations (admittedDeclarations input)) ps) ->
  (env : carrier (commonEnvironmentSetoid [LBool])) -> (v : Fin 1 -> DM) ->
  applyMorphism (dependentPathSemantics (pathWitness (equalityLeft (admittedEquality input))) v) (env, ps) =
  applyMorphism (dependentPathSemantics (pathWitness (equalityRight (admittedEquality input))) v) (env, ps)
openSound input ps adm env v =
  dependentEndpointFaceEvidenceSound (equalityEvidence (admittedEquality input) ps adm) env v Refl

openRuns : Bool
openRuns = case admitCommonEquality budget [LBool] openDecls STop openRaw openRaw LBool
  (AETrans openRaw (AESym AERefl) AERefl) of
    Left _ => False
    Right input => let w = pathWitness (equalityLeft (admittedEquality input)) in
      not (applyMorphism (dependentPathSemantics w (\_ => (False, False))) ((False, ()), openPaths)) &&
      applyMorphism (dependentPathSemantics w (\_ => (True, True))) ((False, ()), openPaths) &&
      (case mapHigherOrderPathDimensions (\_ => the (ScopedInterval 0) One) w of
        MkHigherOrderPathWitness _ mapped => applyMorphism (dependentPathSemantics mapped absurd) ((False, ()), openPaths))

leaf : AdmissionPathTerm 0 k 0
leaf = APOrdinary (ABool True)

-- Both type-check to Bool with identical erasure, but domain annotations differ.
ambiguous : LogicalType -> AdmissionPathTerm 0 0 0
ambiguous a = APApp (LArrow a a) (APLam (APOrdinary (ABool True))) (APLam (APOrdinary (AVar FZ)))

sameErasure : eraseAdmissionPath (Tests.Cubical.CommonEqualityAdmission.ambiguous LBool) =
  eraseAdmissionPath (Tests.Cubical.CommonEqualityAdmission.ambiguous LUnit)
sameErasure = Refl

largeFace : Nat -> ScopedFace 0
largeFace Z = STop
largeFace (S n) = SConjunction STop (largeFace n)

largeCert : Nat -> AdmissionEquality 0 0 0
largeCert Z = AERefl
largeCert (S n) = AESym (largeCert n)

manyLambdas : Nat -> AdmissionTerm n
manyLambdas Z = ABool True
manyLambdas (S n) = ALam (manyLambdas n)

export
checks : List (String, Bool)
checks =
  [ ("CommonEqualityAdmission exact source Bool If shadow image with independent linear Uses", sourceReflRuns)
  , ("CommonEqualityAdmission linear source Bool If congruence and automatic soundness", linearRuns)
  , ("CommonEqualityAdmission arbitrary higher-order lambda/app reflexivity", accepted
      (admitCommonEquality budget [LBool] ADNil STop appRaw appRaw LBool AERefl))
  , ("CommonEqualityAdmission application congruence with actual domain", accepted
      (admitCommonEquality budget [LBool] ADNil STop appRaw appRaw LBool (AEApp (LArrow LBool LBool) AERefl AERefl)))
  , ("CommonEqualityAdmission unit congruence", accepted
      (admitCommonEquality budget [] ADNil STop unitRaw unitRaw LBool (AEUnitElim AERefl AERefl)))
  , ("CommonEqualityAdmission open named path observations and uniform soundness provider", openRuns)
  , ("CommonEqualityAdmission rejects wrong intermediate syntax", syntaxMismatch
      (admitCommonEquality budget [] ADNil STop leaf leaf LBool (AETrans (APOrdinary (ABool False)) AERefl AERefl)))
  , ("CommonEqualityAdmission rejects distinct annotations despite identical erasure", syntaxMismatch
      (admitCommonEquality budget [] ADNil STop (ambiguous LBool) (ambiguous LUnit) LBool AERefl))
  , ("CommonEqualityAdmission rejects intermediate annotation ambiguity", syntaxMismatch
      (admitCommonEquality budget [] ADNil STop (ambiguous LBool) (ambiguous LBool) LBool
        (AETrans (ambiguous LUnit) AERefl AERefl)))
  , ("CommonEqualityAdmission rejects certificate application domain", typeMismatch
      (admitCommonEquality budget [LBool] ADNil STop appRaw appRaw LBool (AEApp LUnit AERefl AERefl)))
  , ("CommonEqualityAdmission rejects changed dimension expression", syntaxMismatch
      (admitCommonEquality budget [LBool] openDecls STop openRaw (APAt FZ (Reverse (Var FZ))) LBool AERefl))
  , ("CommonEqualityAdmission rejects changed ordinary context", typeMismatch
      (admitCommonEquality budget [LUnit] ADNil (the (ScopedFace 0) STop)
        (APOrdinary (AVar FZ)) (APOrdinary (AVar FZ)) LBool AERefl))
  , ("CommonEqualityAdmission checks nonzero ordinary index", accepted
      (admitCommonEquality budget [LUnit, LBool] ADNil (the (ScopedFace 0) STop)
        (APOrdinary (AVar (FS FZ))) (APOrdinary (AVar (FS FZ))) LBool AERefl))
  , ("CommonEqualityAdmission rejects wrong expected result", typeMismatch
      (admitCommonEquality budget [] ADNil STop leaf leaf LUnit AERefl))
  , ("CommonEqualityAdmission independently checks declaration left endpoint", typeMismatch
      (admitCommonEquality budget [] (ADCons LBool AUnit (ABool True) ADNil) STop leaf leaf LBool AERefl))
  , ("CommonEqualityAdmission independently checks declaration right endpoint", typeMismatch
      (admitCommonEquality budget [] (ADCons LBool (ABool True) AUnit ADNil) STop leaf leaf LBool AERefl))
  , ("CommonEqualityAdmission checks actual named index type", typeMismatch
      (admitCommonEquality budget [] (ADCons LUnit AUnit AUnit (ADCons LBool (ABool True) (ABool False) ADNil))
        (the (ScopedFace 1) STop) (APAt FZ (Var FZ)) (APAt FZ (Var FZ)) LBool AERefl))
  , ("CommonEqualityAdmission nonzero named index", accepted
      (admitCommonEquality budget [] (ADCons LUnit AUnit AUnit (ADCons LBool (ABool True) (ABool False) ADNil))
        (the (ScopedFace 1) STop) (APAt (FS FZ) (Var FZ)) (APAt (FS FZ) (Var FZ)) LBool AERefl))
  , ("CommonEqualityAdmission no beta fallback", syntaxMismatch
      (admitCommonEquality budget [] ADNil STop
        (APApp LBool (APLam (APOrdinary (AVar FZ))) leaf) leaf LBool AERefl))
  , ("CommonEqualityAdmission endpoint explicitly unsupported", unsupported
      (admitCommonEquality budget [LBool] openDecls (SEndpoint FZ False) openRaw
        (APOrdinary (AVar FZ)) LBool (AEEndpoint FZ (Var FZ) False)))
  , ("CommonEqualityAdmission restriction explicitly unsupported", unsupported
      (admitCommonEquality budget [] ADNil STop leaf leaf LBool (AERestrict SBottom AERefl)))
  , ("CommonEqualityAdmission shared check fuel leaf exact 3/4", checkingLimited
      (admitCommonEquality (MkAdmissionBudget 100 3) [] ADNil STop leaf leaf LBool AERefl) && accepted
      (admitCommonEquality (MkAdmissionBudget 100 4) [] ADNil STop leaf leaf LBool AERefl))
  , ("CommonEqualityAdmission shared trans siblings exact 5/6", checkingLimited
      (admitCommonEquality (MkAdmissionBudget 100 5) [] ADNil STop leaf leaf LBool (AETrans leaf AERefl AERefl)) && accepted
      (admitCommonEquality (MkAdmissionBudget 100 6) [] ADNil STop leaf leaf LBool (AETrans leaf AERefl AERefl)))
  , ("CommonEqualityAdmission shared if siblings exact 11/12", checkingLimited
      (admitCommonEquality (MkAdmissionBudget 100 11) [LBool] ADNil STop linearRaw linearRaw LBool
        (AEIf AERefl AERefl AERefl)) && accepted
      (admitCommonEquality (MkAdmissionBudget 100 12) [LBool] ADNil STop linearRaw linearRaw LBool
        (AEIf AERefl AERefl AERefl)))
  , ("CommonEqualityAdmission shared preflight exact 9/10", inputLimited
      (admitCommonEquality (MkAdmissionBudget 9 10) [] ADNil STop leaf leaf LBool AERefl) && accepted
      (admitCommonEquality (MkAdmissionBudget 10 10) [] ADNil STop leaf leaf LBool AERefl))
  , ("CommonEqualityAdmission preflights face before checking", inputLimited
      (admitCommonEquality (MkAdmissionBudget 30 0) [] ADNil (largeFace 1000) leaf leaf LBool AERefl))
  , ("CommonEqualityAdmission preflights entire certificate before checking", inputLimited
      (admitCommonEquality (MkAdmissionBudget 30 0) [] ADNil STop leaf leaf LBool (largeCert 1000)))
  , ("CommonEqualityAdmission preflights middle syntax before equality", inputLimited
      (admitCommonEquality (MkAdmissionBudget 30 0) [] ADNil STop leaf leaf LBool
        (AETrans (APOrdinary (manyLambdas 1000)) AERefl AERefl)))
  , ("CommonEqualityAdmission preflights every declaration endpoint", inputLimited
      (admitCommonEquality (MkAdmissionBudget 30 0) [] (ADCons LBool (ABool True) (manyLambdas 1000) ADNil)
        STop leaf leaf LBool AERefl))
  , ("CommonEqualityAdmission preflights unsupported nested input", inputLimited
      (admitCommonEquality (MkAdmissionBudget 30 0) [] ADNil STop leaf leaf LBool (AERestrict (largeFace 1000) AERefl)))
  ]
