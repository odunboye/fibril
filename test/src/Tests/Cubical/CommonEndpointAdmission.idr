module Tests.Cubical.CommonEndpointAdmission

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

budget : CanonicalEqualityBudget
budget = MkCanonicalEqualityBudget (MkAdmissionBudget 2000 200) 10

accepted : Either AdmissionError a -> Bool
accepted (Right _) = True
accepted _ = False

rejectedAs : (AdmissionError -> Bool) -> Either AdmissionError a -> Bool
rejectedAs p (Left err) = p err
rejectedAs p _ = False

syntaxMismatch : AdmissionError -> Bool
syntaxMismatch SyntaxMismatch = True
syntaxMismatch _ = False

typeMismatch : AdmissionError -> Bool
typeMismatch TypeMismatch = True
typeMismatch _ = False

faceMismatch : AdmissionError -> Bool
faceMismatch FaceMismatch = True
faceMismatch _ = False

inputLimited : AdmissionError -> Bool
inputLimited InputLimit = True
inputLimited _ = False

checkingLimited : AdmissionError -> Bool
checkingLimited CheckingLimit = True
checkingLimited _ = False

solverLimited : AdmissionError -> Bool
solverLimited SolverLimit = True
solverLimited _ = False

-- Quantities remain an independent source proof; none enter admission.
linearIf : Term [BoolTy] BoolTy
linearIf = If (Ref Here) (Boolean False) (Boolean True)

linearUses : Uses Tests.Cubical.CommonEndpointAdmission.linearIf [Linear]
linearUses = UseIf (UseRef Here) UseBoolean UseBoolean

endpoint : AdmissionTerm 1
endpoint = AIf (AVar FZ) (ABool False) (ABool True)

sourceImage : eraseAdmission Tests.Cubical.CommonEndpointAdmission.endpoint =
  commonTerm (shadowTerm Tests.Cubical.CommonEndpointAdmission.linearIf)
sourceImage = Refl

declarations : AdmissionDeclarations 1 1
declarations = ADCons LBool (AVar FZ) endpoint ADNil

atPath : AdmissionPathTerm 1 1 2
atPath = APAt FZ (Var FZ)

leftEndpoint : AdmissionPathTerm 1 1 2
leftEndpoint = APOrdinary (AVar FZ)

rightEndpoint : AdmissionPathTerm 1 1 2
rightEndpoint = APOrdinary endpoint

endpointCert : Bool -> AdmissionEquality n (S k) (S d)
endpointCert side = AEEndpoint FZ (Var FZ) side

openValue : Bool -> DM -> Bool
openValue b (side, other) = if side then not b else b

openPaths : carrier (commonDependentPathEnvironmentSetoid [LBool] [LBool])
openPaths = (MkCommonMorphism (\input => openValue (fst (fst input)) (snd input))
  (\{x}, {y}, rel => cong2 openValue (fst (fst rel)) (snd rel)), ())

-- Constructive validity for this particular model and exact admitted witnesses.
-- No assertion that arbitrary contexts have such an interpretation is used.
modelFor : (ds : AdmittedDeclarations [LBool] Tests.Cubical.CommonEndpointAdmission.declarations) ->
  CanonicalPathAdmissible ds Tests.Cubical.CommonEndpointAdmission.openPaths
modelFor (CheckedDeclare (MkAdmittedTerm _ (HOVar _ _ LHere))
  (MkAdmittedTerm _ (HOIf _ _ (HOVar _ _ LHere) (HOBool _ False) (HOBool _ True))) CheckedNoPaths) =
  ((\(b, ()) => Refl), (\(b, ()) => case b of False => Refl; True => Refl), ())

boolEqualityObserved : {x, y : Bool} -> x = y -> Bool
boolEqualityObserved Refl = True

valuation : Bool -> Fin 2 -> DM
valuation side FZ = (side, side)
valuation side (FS FZ) = (False, True)

valuationHolds : (side : Bool) -> faceAtVal (valuation side) (SEndpoint FZ side) = True
valuationHolds False = Refl
valuationHolds True = Refl

-- Invoke the returned provider and authoritative soundness under genuine
-- canonical admissibility, for BOTH ordinary Boolean environments and endpoints.
endpointRuns : (side : Bool) -> Bool
endpointRuns side =
  let target = if side then rightEndpoint else leftEndpoint in
  case admitCanonicalCommonEquality budget [LBool] declarations (SEndpoint FZ side) atPath target LBool (endpointCert side) of
    Left _ => False
    Right input =>
      let e = canonicalResult input
          valid = modelFor (canonicalDeclarations input)
          evidence = canonicalEvidence e openPaths valid
          soundFalse = dependentEndpointFaceEvidenceSound evidence (False, ()) (valuation side) (valuationHolds side)
          soundTrue = dependentEndpointFaceEvidenceSound evidence (True, ()) (valuation side) (valuationHolds side)
          l = pathWitness (canonicalLeft e)
          r = pathWitness (canonicalRight e)
      in boolEqualityObserved soundFalse && boolEqualityObserved soundTrue &&
        (applyMorphism (dependentPathSemantics l (valuation side)) ((False, ()), openPaths) == side) &&
        (applyMorphism (dependentPathSemantics r (valuation side)) ((True, ()), openPaths) == not side)

soundRuns : (side : Bool) -> (left, right : AdmissionPathTerm 1 1 2) -> AdmissionEquality 1 1 2 -> Bool
soundRuns side left right cert =
  case admitCanonicalCommonEquality budget [LBool] declarations (SEndpoint FZ side) left right LBool cert of
    Left _ => False
    Right input => let evidence = canonicalEvidence (canonicalResult input) openPaths (modelFor (canonicalDeclarations input)) in
      boolEqualityObserved (dependentEndpointFaceEvidenceSound evidence (False, ()) (valuation side) (valuationHolds side)) &&
      boolEqualityObserved (dependentEndpointFaceEvidenceSound evidence (True, ()) (valuation side) (valuationHolds side))

app : AdmissionPathTerm 1 1 2 -> AdmissionPathTerm 1 1 2
app x = APApp LBool (APOrdinary (ALam (AVar FZ))) x

conditional : AdmissionPathTerm 1 1 2 -> AdmissionPathTerm 1 1 2
conditional x = APIf (APOrdinary (AVar FZ)) x (APOrdinary (ABool False))

unitElim : AdmissionPathTerm 1 1 2 -> AdmissionPathTerm 1 1 2
unitElim x = APUnitElim (APOrdinary AUnit) x

restrictionRuns : Bool
restrictionRuns = case admitCanonicalCommonEquality budget [LBool] declarations
  (SConjunction (SEndpoint FZ True) STop) atPath rightEndpoint LBool
  (AERestrict (SEndpoint FZ True) (endpointCert True)) of
    Left _ => False
    Right input => boolEqualityObserved (dependentEndpointFaceEvidenceSound
      (canonicalEvidence (canonicalResult input) openPaths (modelFor (canonicalDeclarations input)))
      (False, ()) (valuation True) Refl)

twoDeclarations : AdmissionDeclarations 1 2
twoDeclarations = ADCons LUnit AUnit AUnit declarations

twoPaths : carrier (commonDependentPathEnvironmentSetoid [LBool] [LUnit, LBool])
twoPaths = (MkCommonMorphism (\_ => ()) (\rel => Refl), openPaths)

twoModel : (ds : AdmittedDeclarations [LBool] Tests.Cubical.CommonEndpointAdmission.twoDeclarations) ->
  CanonicalPathAdmissible ds Tests.Cubical.CommonEndpointAdmission.twoPaths
twoModel (CheckedDeclare (MkAdmittedTerm _ (HOUnit _)) (MkAdmittedTerm _ (HOUnit _)) rest) =
  ((\env => Refl), (\env => Refl), modelFor rest)

nonzeroRuns : Bool
nonzeroRuns = case admitCanonicalCommonEquality budget [LBool] twoDeclarations (the (ScopedFace 2) (SEndpoint FZ True))
  (APAt (FS FZ) (Var FZ)) (APOrdinary endpoint) LBool (AEEndpoint (FS FZ) (Var FZ) True) of
    Left _ => False
    Right input => boolEqualityObserved (dependentEndpointFaceEvidenceSound
      (canonicalEvidence (canonicalResult input) twoPaths (twoModel (canonicalDeclarations input)))
      (True, ()) (valuation True) Refl)

mappedRuns : Bool
mappedRuns = case admitCanonicalCommonEquality budget [LBool] declarations (SEndpoint FZ True)
  atPath rightEndpoint LBool (endpointCert True) of
    Left _ => False
    Right input => case mapHigherOrderPathDimensions (\_ => the (ScopedInterval 0) One)
      (pathWitness (canonicalLeft (canonicalResult input))) of
        MkHigherOrderPathWitness _ w => applyMorphism (dependentPathSemantics w absurd) ((False, ()), openPaths)

ambiguous : LogicalType -> AdmissionTerm 0
ambiguous a = AApp (LArrow a a) (ALam (ABool True)) (ALam (AVar FZ))

sameErasure : eraseAdmission (Tests.Cubical.CommonEndpointAdmission.ambiguous LBool) =
  eraseAdmission (Tests.Cubical.CommonEndpointAdmission.ambiguous LUnit)
sameErasure = Refl

smallDecls : AdmissionDeclarations 0 1
smallDecls = ADCons LBool (ABool True) (ABool False) ADNil

smallAt : AdmissionPathTerm 0 1 0
smallAt = APAt FZ Zero

smallTarget : AdmissionPathTerm 0 1 0
smallTarget = APOrdinary (ABool True)

smallCert : AdmissionEquality 0 1 0
smallCert = AEEndpoint FZ Zero False

small : CanonicalEqualityBudget -> Either AdmissionError
  (AdmittedCanonicalEqualityInput [] Tests.Cubical.CommonEndpointAdmission.smallDecls STop
    Tests.Cubical.CommonEndpointAdmission.smallAt Tests.Cubical.CommonEndpointAdmission.smallTarget LBool)
small b = admitCanonicalCommonEquality b [] smallDecls STop smallAt smallTarget LBool smallCert

largeFace : Nat -> ScopedFace d
largeFace Z = STop
largeFace (S n) = SConjunction STop (largeFace n)

largeInterval : Nat -> ScopedInterval d
largeInterval Z = Zero
largeInterval (S n) = Reverse (largeInterval n)

largeTerm : Nat -> AdmissionTerm n
largeTerm Z = ABool True
largeTerm (S n) = ALam (largeTerm n)

largeCertificate : Nat -> AdmissionEquality n k d
largeCertificate Z = AERefl
largeCertificate (S n) = AESym (largeCertificate n)

largeType : Nat -> LogicalType
largeType Z = LBool
largeType (S n) = LArrow LBool (largeType n)

export
checks : List (String, Bool)
checks =
  [ ("CommonEndpointAdmission genuine open named path both endpoints and automatic canonical soundness", endpointRuns False && endpointRuns True)
  , ("CommonEndpointAdmission symmetry on genuinely different terms", soundRuns True rightEndpoint atPath (AESym (endpointCert True)))
  , ("CommonEndpointAdmission transitivity with genuinely different middle and checked ordinary alignment", soundRuns True atPath rightEndpoint
      (AETrans rightEndpoint (endpointCert True) AERefl))
  , ("CommonEndpointAdmission transitivity checks named path alignment", soundRuns False leftEndpoint atPath
      (AETrans atPath (AESym (endpointCert False)) AERefl))
  , ("CommonEndpointAdmission nonreflexive application congruence and canonical soundness", soundRuns True (app atPath) (app rightEndpoint)
      (AEApp LBool AERefl (endpointCert True)))
  , ("CommonEndpointAdmission nonreflexive If congruence and canonical soundness", soundRuns False (conditional atPath) (conditional leftEndpoint)
      (AEIf AERefl (endpointCert False) AERefl))
  , ("CommonEndpointAdmission nonreflexive unit congruence and canonical soundness", soundRuns True (unitElim atPath) (unitElim rightEndpoint)
      (AEUnitElim AERefl (endpointCert True)))
  , ("CommonEndpointAdmission structural application/lambda/variable trans middle", soundRuns True (app atPath) (app rightEndpoint)
      (AETrans (app rightEndpoint) (AEApp LBool AERefl (endpointCert True)) AERefl))
  , ("CommonEndpointAdmission structural If trans middle", soundRuns True (conditional atPath) (conditional rightEndpoint)
      (AETrans (conditional rightEndpoint) (AEIf AERefl (endpointCert True) AERefl) AERefl))
  , ("CommonEndpointAdmission structural unit trans middle", soundRuns True (unitElim atPath) (unitElim rightEndpoint)
      (AETrans (unitElim rightEndpoint) (AEUnitElim AERefl (endpointCert True)) AERefl))
  , ("CommonEndpointAdmission correctly directed restriction and automatic soundness", restrictionRuns)
  , ("CommonEndpointAdmission exact nonzero named lookup canonical soundness", nonzeroRuns)
  , ("CommonEndpointAdmission returned witness dimension mapping observation", mappedRuns)
  , ("CommonEndpointAdmission rejects wrong face", rejectedAs faceMismatch
      (admitCanonicalCommonEquality budget [LBool] declarations (SEndpoint FZ False) atPath rightEndpoint LBool (endpointCert True)))
  , ("CommonEndpointAdmission rejects unconstrained/non-Boolean endpoint face", rejectedAs faceMismatch
      (admitCanonicalCommonEquality budget [LBool] declarations STop atPath rightEndpoint LBool (endpointCert True)))
  , ("CommonEndpointAdmission rejects reversed restriction implication", rejectedAs faceMismatch
      (admitCanonicalCommonEquality budget [LBool] declarations STop atPath rightEndpoint LBool
        (AERestrict (SEndpoint FZ True) (endpointCert True))))
  , ("CommonEndpointAdmission rejects wrong name", rejectedAs syntaxMismatch
      (admitCanonicalCommonEquality budget [LBool] twoDeclarations (the (ScopedFace 2) (SEndpoint FZ True))
        (APAt (FS FZ) (Var FZ)) (APOrdinary endpoint) LBool (AEEndpoint FZ (Var FZ) True)))
  , ("CommonEndpointAdmission rejects wrong actual declared result type", rejectedAs typeMismatch
      (admitCanonicalCommonEquality budget [LBool] twoDeclarations (the (ScopedFace 2) (SEndpoint FZ True))
        (APAt FZ (Var FZ)) (APOrdinary endpoint) LBool (AEEndpoint FZ (Var FZ) True)))
  , ("CommonEndpointAdmission rejects changed ordinary context", rejectedAs typeMismatch
      (admitCanonicalCommonEquality budget [LUnit] declarations (SEndpoint FZ True) atPath rightEndpoint LBool (endpointCert True)))
  , ("CommonEndpointAdmission rejects changed interval syntax", rejectedAs syntaxMismatch
      (admitCanonicalCommonEquality budget [LBool] declarations (SEndpoint FZ True) atPath rightEndpoint LBool
        (AEEndpoint FZ (Reverse (Var FZ)) True)))
  , ("CommonEndpointAdmission rejects wrong endpoint target", rejectedAs syntaxMismatch
      (admitCanonicalCommonEquality budget [LBool] declarations (SEndpoint FZ True) atPath leftEndpoint LBool (endpointCert True)))
  , ("CommonEndpointAdmission rejects same-erasure target annotation mismatch", rejectedAs syntaxMismatch
      (admitCanonicalCommonEquality budget [] (ADCons LBool (ambiguous LBool) (ABool False) ADNil)
        (the (ScopedFace 0) STop) (APAt FZ Zero) (APOrdinary (ambiguous LUnit)) LBool (AEEndpoint FZ Zero False)))
  , ("CommonEndpointAdmission rejects wrong declared endpoint typing independently", rejectedAs typeMismatch
      (admitCanonicalCommonEquality budget [] (ADCons LBool (ABool True) AUnit ADNil)
        STop smallAt smallTarget LBool smallCert))
  , ("CommonEndpointAdmission no beta fallback", rejectedAs syntaxMismatch
      (admitCanonicalCommonEquality budget [] smallDecls STop smallAt
        (APApp LBool (APLam (APOrdinary (AVar FZ))) smallTarget) LBool smallCert))
  , ("CommonEndpointAdmission exact shared input boundary 16/17", rejectedAs inputLimited
      (small (MkCanonicalEqualityBudget (MkAdmissionBudget 16 10) 1)) && accepted
      (small (MkCanonicalEqualityBudget (MkAdmissionBudget 17 10) 1)))
  , ("CommonEndpointAdmission exact shared checking boundary 4/5", rejectedAs checkingLimited
      (small (MkCanonicalEqualityBudget (MkAdmissionBudget 100 4) 1)) && accepted
      (small (MkCanonicalEqualityBudget (MkAdmissionBudget 100 5) 1)))
  , ("CommonEndpointAdmission explicit solver call exhaustion", rejectedAs solverLimited
      (small (MkCanonicalEqualityBudget (MkAdmissionBudget 100 100) 0)))
  , ("CommonEndpointAdmission solver calls threaded across trans/sym", rejectedAs solverLimited
      (admitCanonicalCommonEquality (MkCanonicalEqualityBudget (MkAdmissionBudget 200 100) 1) [] smallDecls STop smallAt smallAt LBool
        (AETrans smallTarget smallCert (AESym smallCert))) && accepted
      (admitCanonicalCommonEquality (MkCanonicalEqualityBudget (MkAdmissionBudget 200 100) 2) [] smallDecls STop smallAt smallAt LBool
        (AETrans smallTarget smallCert (AESym smallCert))))
  , ("CommonEndpointAdmission checking fuel threaded across trans/sym 7/8", rejectedAs checkingLimited
      (admitCanonicalCommonEquality (MkCanonicalEqualityBudget (MkAdmissionBudget 200 7) 2) [] smallDecls STop smallAt smallAt LBool
        (AETrans smallTarget smallCert (AESym smallCert))) && accepted
      (admitCanonicalCommonEquality (MkCanonicalEqualityBudget (MkAdmissionBudget 200 8) 2) [] smallDecls STop smallAt smallAt LBool
        (AETrans smallTarget smallCert (AESym smallCert))))
  , ("CommonEndpointAdmission solver allowance shared across all congruence siblings", rejectedAs solverLimited
      (admitCanonicalCommonEquality (MkCanonicalEqualityBudget (MkAdmissionBudget 200 100) 2) [] smallDecls STop
        (APIf smallAt smallAt smallAt) (APIf smallTarget smallTarget smallTarget) LBool (AEIf smallCert smallCert smallCert)) && accepted
      (admitCanonicalCommonEquality (MkCanonicalEqualityBudget (MkAdmissionBudget 200 100) 3) [] smallDecls STop
        (APIf smallAt smallAt smallAt) (APIf smallTarget smallTarget smallTarget) LBool (AEIf smallCert smallCert smallCert)))
  , ("CommonEndpointAdmission restriction and endpoint share solver allowance", rejectedAs solverLimited
      (admitCanonicalCommonEquality (MkCanonicalEqualityBudget (MkAdmissionBudget 200 100) 1) [] smallDecls STop smallAt smallTarget LBool
        (AERestrict STop smallCert)))
  , ("CommonEndpointAdmission bounded interval expansion rejects inconclusively", rejectedAs faceMismatch
      (admitCanonicalCommonEquality budget [] smallDecls STop (APAt FZ (largeInterval 20)) smallTarget LBool
        (AEEndpoint FZ (largeInterval 20) False)))
  , ("CommonEndpointAdmission authoritative solver face cap rejects inconclusively", rejectedAs faceMismatch
      (admitCanonicalCommonEquality budget [] smallDecls (largeFace 20) smallAt smallTarget LBool smallCert))
  , ("CommonEndpointAdmission preflights face before any checking/solver", rejectedAs inputLimited
      (admitCanonicalCommonEquality (MkCanonicalEqualityBudget (MkAdmissionBudget 30 0) 0) [] smallDecls (largeFace 1000) smallAt smallTarget LBool smallCert))
  , ("CommonEndpointAdmission preflights entire raw target before any checking/solver", rejectedAs inputLimited
      (admitCanonicalCommonEquality (MkCanonicalEqualityBudget (MkAdmissionBudget 30 0) 0) [] smallDecls STop smallAt
        (APOrdinary (largeTerm 1000)) LBool smallCert))
  , ("CommonEndpointAdmission preflights every declared endpoint before checking/solver", rejectedAs inputLimited
      (admitCanonicalCommonEquality (MkCanonicalEqualityBudget (MkAdmissionBudget 30 0) 0) []
        (ADCons LBool (ABool True) (largeTerm 1000) ADNil) STop smallAt smallTarget LBool smallCert))
  , ("CommonEndpointAdmission preflights all certificate branches before checking/solver", rejectedAs inputLimited
      (admitCanonicalCommonEquality (MkCanonicalEqualityBudget (MkAdmissionBudget 30 0) 0) [] smallDecls STop smallAt smallTarget LBool
        (AETrans smallAt smallCert (largeCertificate 1000))))
  , ("CommonEndpointAdmission preflights certificate intervals before checking/solver", rejectedAs inputLimited
      (admitCanonicalCommonEquality (MkCanonicalEqualityBudget (MkAdmissionBudget 30 0) 0) [] smallDecls STop smallAt smallTarget LBool
        (AEEndpoint FZ (largeInterval 1000) False)))
  , ("CommonEndpointAdmission rejects wrong expected type", rejectedAs typeMismatch
      (admitCanonicalCommonEquality budget [] smallDecls STop smallAt smallTarget LUnit smallCert))
  , ("CommonEndpointAdmission independently checks left declared endpoint", rejectedAs typeMismatch
      (admitCanonicalCommonEquality budget [] (ADCons LBool AUnit (ABool False) ADNil)
        STop smallAt smallTarget LBool smallCert))
  , ("CommonEndpointAdmission preflights context before any checking/solver", rejectedAs inputLimited
      (admitCanonicalCommonEquality (MkCanonicalEqualityBudget (MkAdmissionBudget 30 0) 0) (replicate 1000 LBool)
        (ADCons LBool (ABool True) (ABool False) ADNil) (the (ScopedFace 0) STop)
        (APAt FZ Zero) (APOrdinary (ABool True)) LBool (AEEndpoint FZ Zero False)))
  , ("CommonEndpointAdmission preflights dimension scope before any checking/solver", rejectedAs inputLimited
      (admitCanonicalCommonEquality (MkCanonicalEqualityBudget (MkAdmissionBudget 30 0) 0) [] smallDecls
        (the (ScopedFace 1000) STop) (APAt FZ Zero) (APOrdinary (ABool True)) LBool (AEEndpoint FZ Zero False)))
  , ("CommonEndpointAdmission preflights raw target annotations before checking/solver", rejectedAs inputLimited
      (admitCanonicalCommonEquality (MkCanonicalEqualityBudget (MkAdmissionBudget 30 0) 0) [] smallDecls STop smallAt
        (APOrdinary (AApp (largeType 1000) (ABool True) (ABool True))) LBool smallCert))
  , ("CommonEndpointAdmission preflights certificate annotations before checking/solver", rejectedAs inputLimited
      (admitCanonicalCommonEquality (MkCanonicalEqualityBudget (MkAdmissionBudget 30 0) 0) [] smallDecls STop smallAt smallTarget LBool
        (AEApp (largeType 1000) AERefl AERefl)))
  , ("CommonEndpointAdmission preflights restriction source face before checking/solver", rejectedAs inputLimited
      (admitCanonicalCommonEquality (MkCanonicalEqualityBudget (MkAdmissionBudget 30 0) 0) [] smallDecls STop smallAt smallTarget LBool
        (AERestrict (largeFace 1000) smallCert)))
  ]
