module Tests.Cubical.CommonAbstractionAdmission

import Data.Fin
import Data.Vect
import Fibril.Core.Quantity
import Fibril.Core.Usage
import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Quantitative.Usage
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.CommonAdmission
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

budget : CanonicalEqualityBudget
budget = MkCanonicalEqualityBudget (MkAdmissionBudget 4000 400) 20

accepted : Either AdmissionError a -> Bool
accepted (Right _) = True
accepted _ = False

rejectedAs : AdmissionError -> Either AdmissionError a -> Bool
rejectedAs InputLimit (Left InputLimit) = True
rejectedAs CheckingLimit (Left CheckingLimit) = True
rejectedAs SolverLimit (Left SolverLimit) = True
rejectedAs SyntaxMismatch (Left SyntaxMismatch) = True
rejectedAs TypeMismatch (Left TypeMismatch) = True
rejectedAs FaceMismatch (Left FaceMismatch) = True
rejectedAs _ _ = False

-- Quantitative source evidence is independent of admission.
linearIf : Term [BoolTy] BoolTy
linearIf = If (Ref Here) (Boolean False) (Boolean True)

linearUses : Uses Tests.Cubical.CommonAbstractionAdmission.linearIf [Linear]
linearUses = UseIf (UseRef Here) UseBoolean UseBoolean

endpoint : AdmissionTerm 1
endpoint = AIf (AVar FZ) (ABool False) (ABool True)

sourceImage : eraseAdmission Tests.Cubical.CommonAbstractionAdmission.endpoint =
  commonTerm (shadowTerm Tests.Cubical.CommonAbstractionAdmission.linearIf)
sourceImage = Refl

declarations : AdmissionDeclarations 1 1
declarations = ADCons LBool (AVar FZ) endpoint ADNil

leftEndpoint : AdmissionPathTerm 1 1 2
leftEndpoint = APOrdinary (AVar FZ)

rightEndpoint : AdmissionPathTerm 1 1 2
rightEndpoint = APOrdinary endpoint

body : AdmissionPathTerm 1 1 3
body = APAt FZ (Var FZ)

cert : Bool -> AdmissionEquality 1 1 3
cert side = AEEndpoint FZ (Var FZ) side

ambient : ScopedFace 2
ambient = SEndpoint FZ False

valuation : Fin 2 -> DM
valuation FZ = (False, False)
valuation (FS FZ) = (False, True)

openValue : Bool -> DM -> Bool
openValue b (side, other) = if side then not b else b

openPaths : carrier (commonDependentPathEnvironmentSetoid [LBool] [LBool])
openPaths = (MkCommonMorphism (\input => openValue (fst (fst input)) (snd input))
  (\{x}, {y}, rel => cong2 openValue (fst (fst rel)) (snd rel)), ())

modelFor : (ds : AdmittedDeclarations [LBool] Tests.Cubical.CommonAbstractionAdmission.declarations) ->
  CanonicalPathAdmissible ds Tests.Cubical.CommonAbstractionAdmission.openPaths
modelFor (CheckedDeclare (MkAdmittedTerm _ (HOVar _ _ LHere))
  (MkAdmittedTerm _ (HOIf _ _ (HOVar _ _ LHere) (HOBool _ False) (HOBool _ True))) CheckedNoPaths) =
  ((\(b, ()) => Refl), (\(b, ()) => case b of False => Refl; True => Refl), ())

observed : {x, y : Bool} -> x = y -> Bool
observed Refl = True

run : (side, b : Bool) -> Bool
run side b = case admitCanonicalCommonAbstraction budget [LBool] declarations ambient
  leftEndpoint rightEndpoint body LBool (cert False) (cert True) of
    Left _ => False
    Right input =>
      let result = abstractionResult input
          witness = abstractionEvidence result openPaths (modelFor (abstractionDeclarations input))
          applied = higherOrderCommonPathApplication witness (if side then One else Zero)
      in observed (higherOrderCommonPathBoundary witness side (b, ()) valuation Refl) &&
         observed (trans (higherOrderCommonPathApplicationRelated witness Zero (b, ()) valuation)
           (higherOrderCommonPathBoundary witness False (b, ()) valuation Refl)) &&
         observed (trans (higherOrderCommonPathApplicationRelated witness One (b, ()) valuation)
           (higherOrderCommonPathBoundary witness True (b, ()) valuation Refl)) &&
         observed (higherOrderCommonPathApplicationRelated witness (Reverse (Var (FS FZ))) (b, ()) valuation) &&
         applyMorphism (dependentPathSemantics (pathWitness applied) valuation) ((b, ()), openPaths) ==
           (if side then not b else b)

identityApplication : AdmissionPathTerm 1 1 d -> AdmissionPathTerm 1 1 d
identityApplication x = APApp LBool (APLam (APOrdinary (AVar FZ))) x

compositeRuns : Bool
compositeRuns = case admitCanonicalCommonAbstraction budget [LBool] declarations ambient
  (identityApplication leftEndpoint) (identityApplication rightEndpoint) (identityApplication body) LBool
  (AETrans (identityApplication body) AERefl (AEApp LBool AERefl (cert False)))
  (AEApp LBool AERefl (cert True)) of
    Left _ => False
    Right input =>
      let witness = abstractionEvidence (abstractionResult input) openPaths (modelFor (abstractionDeclarations input))
      in observed (higherOrderCommonPathBoundary witness False (False, ()) valuation Refl) &&
         observed (higherOrderCommonPathBoundary witness True (True, ()) valuation Refl) &&
         observed (higherOrderCommonPathApplicationRelated witness (Var (FS FZ)) (True, ()) valuation)

-- Dimension-dependent endpoints are weakened at FS, not captured by FZ.
dependentEndpoint : AdmissionPathTerm 1 1 2
dependentEndpoint = APAt FZ (Reverse (Meet (Var (FS FZ)) (Var FZ)))

dependentRuns : Bool
dependentRuns = case admitCanonicalCommonAbstraction budget [LBool] declarations ambient
  dependentEndpoint dependentEndpoint (weakenAdmissionPath dependentEndpoint) LBool AERefl AERefl of
    Left _ => False
    Right input =>
      let witness = abstractionEvidence (abstractionResult input) openPaths (modelFor (abstractionDeclarations input))
      in observed (higherOrderCommonPathBoundary witness False (False, ()) valuation Refl) &&
         observed (higherOrderCommonPathBoundary witness True (True, ()) valuation Refl) &&
         observed (higherOrderCommonPathApplicationRelated witness (Var (FS FZ)) (True, ()) valuation) &&
         applyMorphism (dependentPathSemantics (pathWitness (higherOrderCommonPathApplication witness Zero)) valuation)
           ((False, ()), openPaths)

-- The returned path is definitionally this exact raw body, not just endpoints.
returnedBody : {ctx : Vect n LogicalType} -> {raw : AdmissionDeclarations n k} ->
  {decls : AdmittedDeclarations ctx raw} -> {body : AdmissionPathTerm n k (S d)} ->
  {left, right : AdmissionPathTerm n k d} ->
  (result : AdmittedCanonicalAbstraction decls face left right body a) -> (i : ScopedInterval d) ->
  applyCommonShadowPath (abstractionPath result) i = mapCommonPathDimensions (atDimension i) (eraseAdmissionPath body)
returnedBody result i = Refl

noPathsValid : (ds : AdmittedDeclarations ctx ADNil) -> CanonicalPathAdmissible ds ()
noPathsValid CheckedNoPaths = ()

-- Lambda captures the ordinary variable across both independent binders.
captured : AdmissionPathTerm 1 0 1
captured = APLam (APOrdinary (AVar (FS FZ)))

capturedRuns : Bool
capturedRuns = case admitCanonicalCommonAbstraction budget [LBool] ADNil STop
  captured captured (weakenAdmissionPath captured) (LArrow LUnit LBool) AERefl AERefl of
    Left _ => False
    Right input =>
      let witness = abstractionEvidence (abstractionResult input) () (noPathsValid (abstractionDeclarations input))
          app = higherOrderCommonPathApplication witness (Var FZ)
          val = the (Fin 1 -> DM) (\FZ => (True, False))
          fn = applyMorphism (dependentPathSemantics (pathWitness app) val) ((True, ()), ())
          sound = higherOrderCommonPathBoundary witness True (False, ()) val Refl
      in applyMorphism fn () && observed (sound () () Refl)

small : CanonicalEqualityBudget -> Either AdmissionError
  (AdmittedCanonicalAbstractionInput [] ADNil STop
    (the (AdmissionPathTerm 0 0 0) (APOrdinary (ABool True)))
    (APOrdinary (ABool True)) (APOrdinary (ABool True)) LBool)
small b = admitCanonicalCommonAbstraction b [] ADNil STop
  (APOrdinary (ABool True)) (APOrdinary (ABool True)) (APOrdinary (ABool True)) LBool AERefl AERefl

limited : Nat -> Nat -> Nat -> CanonicalEqualityBudget
limited i c s = MkCanonicalEqualityBudget (MkAdmissionBudget i c) s

-- Both alternatives are well typed and erase alike, but annotations differ.
ambiguousEndpoint : LogicalType -> AdmissionTerm 1
ambiguousEndpoint a = AApp (LArrow a a) (ALam (ABool True)) (ALam (AVar FZ))

sameErasure : eraseAdmission (ambiguousEndpoint LUnit) = eraseAdmission (ambiguousEndpoint LBool)
sameErasure = Refl

public export
checks : List (String, Bool)
checks =
  [ ("CommonAbstractionAdmission actual nonconstant abstraction both endpoints/environments and exact application theorem", run False False && run False True && run True False && run True True)
  , ("CommonAbstractionAdmission application/lambda/trans boundary structural alignment", compositeRuns)
  , ("CommonAbstractionAdmission dimension-dependent endpoint capture-avoiding weakening", dependentRuns)
  , ("CommonAbstractionAdmission arrow body captures ordinary variable", capturedRuns)
  , ("CommonAbstractionAdmission exact input expansion reservation 31/32", rejectedAs InputLimit (small (limited 31 13 0)) && accepted (small (limited 32 13 0)))
  , ("CommonAbstractionAdmission expansion reservation precedes checking", rejectedAs InputLimit (small (limited 31 0 0)) && rejectedAs CheckingLimit (small (limited 32 0 0)))
  , ("CommonAbstractionAdmission shared checking 12/13 second boundary exhaustion", rejectedAs CheckingLimit (small (limited 32 12 0)) && accepted (small (limited 32 13 0)))
  , ("CommonAbstractionAdmission first boundary exhausts shared checking", rejectedAs CheckingLimit (small (limited 32 9 0)))
  , ("CommonAbstractionAdmission second boundary shares solver tokens", rejectedAs SolverLimit
      (admitCanonicalCommonAbstraction (limited 4000 400 1) [LBool] declarations ambient leftEndpoint rightEndpoint body LBool (cert False) (cert True)))
  , ("CommonAbstractionAdmission wrong right boundary side/target", rejectedAs SyntaxMismatch
      (admitCanonicalCommonAbstraction budget [LBool] declarations ambient leftEndpoint rightEndpoint body LBool (cert False) (cert False)))
  , ("CommonAbstractionAdmission wrong actual second boundary face", rejectedAs FaceMismatch
      (admitCanonicalCommonAbstraction budget [LBool] declarations ambient leftEndpoint rightEndpoint body LBool
        (cert False) (AERestrict (SEndpoint FZ False) (cert True))))
  , ("CommonAbstractionAdmission malformed second boundary", rejectedAs SyntaxMismatch
      (admitCanonicalCommonAbstraction budget [LBool] declarations ambient leftEndpoint rightEndpoint body LBool (cert False) AERefl))
  , ("CommonAbstractionAdmission wrong first boundary", rejectedAs SyntaxMismatch
      (admitCanonicalCommonAbstraction budget [LBool] declarations ambient leftEndpoint rightEndpoint body LBool AERefl (cert True)))
  , ("CommonAbstractionAdmission changed context", rejectedAs TypeMismatch
      (admitCanonicalCommonAbstraction budget [LUnit] declarations ambient leftEndpoint rightEndpoint body LBool (cert False) (cert True)))
  , ("CommonAbstractionAdmission wrong result type", rejectedAs TypeMismatch
      (admitCanonicalCommonAbstraction budget [LBool] declarations ambient leftEndpoint rightEndpoint body LUnit (cert False) (cert True)))
  , ("CommonAbstractionAdmission body independently typechecked", rejectedAs TypeMismatch
      (admitCanonicalCommonAbstraction budget [LBool] declarations ambient leftEndpoint rightEndpoint (APOrdinary AUnit) LBool AERefl AERefl))
  , ("CommonAbstractionAdmission exact endpoint annotation despite same erasure", rejectedAs SyntaxMismatch
      (admitCanonicalCommonAbstraction budget [LBool] (ADCons LBool (ambiguousEndpoint LUnit) (ambiguousEndpoint LUnit) ADNil) STop
        (the (AdmissionPathTerm 1 1 0) (APOrdinary (ambiguousEndpoint LBool))) (APOrdinary (ambiguousEndpoint LUnit))
        (APAt FZ (Var FZ)) LBool (AEEndpoint FZ (Var FZ) False) (AEEndpoint FZ (Var FZ) True)))
  , ("CommonAbstractionAdmission full second certificate preflight precedes checking/solver", rejectedAs InputLimit
      (admitCanonicalCommonAbstraction (limited 45 0 0) [LBool] declarations ambient leftEndpoint rightEndpoint body LBool
        (cert False) (AETrans body (AESym (AESym (cert True))) (AESym (AESym (cert True))))))
  , ("CommonAbstractionAdmission full first certificate preflight precedes checking/solver", rejectedAs InputLimit
      (admitCanonicalCommonAbstraction (limited 45 0 0) [LBool] declarations ambient leftEndpoint rightEndpoint body LBool
        (AETrans body (AESym (AESym (cert False))) (AESym (AESym (cert False)))) (cert True)))
  , ("CommonAbstractionAdmission all declarations preflight precedes checking", rejectedAs InputLimit
      (admitCanonicalCommonAbstraction (limited 4 0 0) [LBool] declarations ambient leftEndpoint rightEndpoint body LBool (cert False) (cert True)))
  , ("CommonAbstractionAdmission well-scoped wrong body dimension syntax", rejectedAs SyntaxMismatch
      (admitCanonicalCommonAbstraction budget [LBool] declarations ambient leftEndpoint rightEndpoint
        (APAt FZ (Var (FS FZ))) LBool (cert False) (cert True)))
  , ("CommonAbstractionAdmission endpoint independently typechecked", rejectedAs TypeMismatch
      (admitCanonicalCommonAbstraction budget [LBool] declarations ambient (APOrdinary AUnit) rightEndpoint body LBool (cert False) (cert True)))
  , ("CommonAbstractionAdmission unselected declaration endpoint independently typechecked", rejectedAs TypeMismatch
      (admitCanonicalCommonAbstraction budget [LBool] (ADCons LBool (AVar FZ) AUnit ADNil) ambient
        leftEndpoint leftEndpoint body LBool (cert False) (cert False)))
  , ("CommonAbstractionAdmission authoritative solver cap rejects without fallback", rejectedAs FaceMismatch
      (admitCanonicalCommonAbstraction budget [LBool] declarations
        (SConjunction ambient (SConjunction ambient (SConjunction ambient (SConjunction ambient (SConjunction ambient ambient)))))
        leftEndpoint rightEndpoint body LBool (cert False) (cert True)))
  , ("CommonAbstractionAdmission missing first solver token", rejectedAs SolverLimit
      (admitCanonicalCommonAbstraction (limited 4000 400 0) [LBool] declarations ambient leftEndpoint rightEndpoint body LBool (cert False) (cert True)))
  , ("CommonAbstractionAdmission type preflight before checking", rejectedAs InputLimit
      (admitCanonicalCommonAbstraction (limited 20 0 0) [LBool] declarations ambient leftEndpoint rightEndpoint body
        (LArrow (LArrow LBool LBool) (LArrow LBool LBool)) (cert False) (cert True)))
  , ("CommonAbstractionAdmission dimension scope preflight before checking", rejectedAs InputLimit
      (admitCanonicalCommonAbstraction (limited 17 0 0) [LBool] declarations ambient leftEndpoint rightEndpoint body LBool (cert False) (cert True)))
  , ("CommonAbstractionAdmission ambient face preflight before checking", rejectedAs InputLimit
      (admitCanonicalCommonAbstraction (limited 19 0 0) [LBool] declarations (SConjunction ambient ambient) leftEndpoint rightEndpoint body LBool (cert False) (cert True)))
  , ("CommonAbstractionAdmission full body preflight before checking", rejectedAs InputLimit
      (admitCanonicalCommonAbstraction (limited 33 0 0) [LBool] declarations ambient leftEndpoint rightEndpoint
        (APIf (APOrdinary (AVar FZ)) body body) LBool (cert False) (cert True)))
  , ("CommonAbstractionAdmission no lambda equality rule invented", rejectedAs SyntaxMismatch
      (admitCanonicalCommonAbstraction budget [LBool] ADNil STop captured captured (weakenAdmissionPath captured)
        (LArrow LUnit LBool) (AEApp LUnit AERefl AERefl) AERefl))
  ]
