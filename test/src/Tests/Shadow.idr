module Tests.Shadow

import Data.Vect
import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Usage
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.PathContext


import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Foundation.DeMorgan.Face


import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Quantitative.Usage

import Fibril.Core.Quantitative.Substitution
import Fibril.Cubical.Logical.ShadowSubstitution
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

import Fibril.Cubical.Logical.Shadow

%default total

quantitiesForgotten : shadowType (Arrow Linear BoolTy UnitTy) = shadowType (Arrow Erased BoolTy UnitTy)
quantitiesForgotten = Refl

nestedShadow :
  shadowTerm (the (Term [BoolTy] (Arrow Linear UnitTy BoolTy))
    (Lam Linear (If (Ref (There Here)) (Boolean True) (Boolean False)))) =
  LLam (LIf (LRef (LThere LHere)) (LBoolean True) (LBoolean False))
nestedShadow = Refl

replaceBool : LogicalSubstitution [LBool] []
replaceBool LHere = LBoolean True

captureAvoided :
  substituteLogical Tests.Shadow.replaceBool (LLam (LRef (LThere LHere))) =
    the (LogicalTerm [] (LArrow LUnit LBool)) (LLam (LBoolean True))
captureAvoided = Refl

unitElimination : shadowTerm (the (Term [] BoolTy) (UnitElim Unit (Boolean False))) =
                  LUnitElim LUnitValue (LBoolean False)
unitElimination = Refl

-- The proof handles all source constructors, including lifting under binders.

sourceReplacement : Substitution [BoolTy] [UnitTy]
sourceReplacement Here = Boolean True

commutesUnderLambda :
  shadowTerm (substitute Tests.Shadow.sourceReplacement
    (the (Term [BoolTy] (Arrow Linear UnitTy BoolTy))
      (Lam Linear (If (Ref (There Here)) (Boolean True) (Boolean False))))) =
  substituteLogical (imageSubstitution [BoolTy] Tests.Shadow.sourceReplacement)
    (shadowTerm (the (Term [BoolTy] (Arrow Linear UnitTy BoolTy))
      (Lam Linear (If (Ref (There Here)) (Boolean True) (Boolean False)))))
commutesUnderLambda = shadowSubstitutionCommutes [BoolTy] Tests.Shadow.sourceReplacement
  (the (Term [BoolTy] (Arrow Linear UnitTy BoolTy))
    (Lam Linear (If (Ref (There Here)) (Boolean True) (Boolean False))))

boolPath : ExactPath {context = [LBool]} {paths = [LBool]} {d = 0}
  (BodyIf (Embed (LRef LHere)) (NeutralAt LHere Zero) (Embed (LBoolean False)))
  (BodyIf (Embed (LRef LHere)) (NeutralAt LHere One) (Embed (LBoolean False)))
boolPath = PathAbstract (BodyIf (Embed (LRef LHere)) (NeutralAt LHere (Var FZ)) (Embed (LBoolean False))) Refl Refl

pathEndpoint : applyExactPath Tests.Shadow.boolPath Zero =
  BodyIf (Embed (LRef LHere)) (NeutralAt LHere Zero) (Embed (LBoolean False))
pathEndpoint = pathAtZero Tests.Shadow.boolPath

pathSubstitution : applyExactPath (substituteExactPath Tests.Shadow.replaceBool Tests.Shadow.boolPath) One =
  BodyIf (Embed (LBoolean True)) (NeutralAt LHere One) (Embed (LBoolean False))
pathSubstitution = pathAtOne (substituteExactPath Tests.Shadow.replaceBool Tests.Shadow.boolPath)

mixedPathSubstitution :
  applyExactPath (substituteExactPath Tests.Shadow.replaceBool Tests.Shadow.boolPath) Zero =
  mapPathTerms Tests.Shadow.replaceBool (applyExactPath Tests.Shadow.boolPath Zero)
mixedPathSubstitution = substitutePathApplication Tests.Shadow.replaceBool Tests.Shadow.boolPath Zero

identityQuantities : Substitution [Arrow Linear BoolTy BoolTy, Arrow Erased BoolTy BoolTy]
                                  [Arrow Linear BoolTy BoolTy, Arrow Erased BoolTy BoolTy]
identityQuantities v = Ref v

collidingTypeImages :
  imageSubstitution [Arrow Linear BoolTy BoolTy, Arrow Erased BoolTy BoolTy]
    Tests.Shadow.identityQuantities (LThere LHere) = LRef (LThere LHere)
collidingTypeImages = Refl

lambdaPath : ExactPath {context = [LBool]} {paths = [LBool]} {d = 0}
  (BodyLam (BodyIf (Embed (LRef (LThere LHere))) (NeutralAt LHere Zero) (Embed (LRef LHere))))
  (BodyLam (BodyIf (Embed (LRef (LThere LHere))) (NeutralAt LHere One) (Embed (LRef LHere))))
lambdaPath = PathAbstract (BodyLam (BodyIf (Embed (LRef (LThere LHere))) (NeutralAt LHere (Var FZ)) (Embed (LRef LHere)))) Refl Refl

lambdaPathSubstitution :
  applyExactPath (substituteExactPath Tests.Shadow.replaceBool Tests.Shadow.lambdaPath) Zero =
  BodyLam (BodyIf (Embed (LBoolean True)) (NeutralAt LHere Zero) (Embed (LRef LHere)))
lambdaPathSubstitution = pathAtZero (substituteExactPath Tests.Shadow.replaceBool Tests.Shadow.lambdaPath)

-- The source condition consumes its sole variable exactly once.
linearSource : Term [BoolTy] BoolTy
linearSource = If (Ref Here) (Boolean True) (Boolean False)

linearSourceUses : Uses Tests.Shadow.linearSource [Linear]
linearSourceUses = UseIf (UseRef Here) UseBoolean UseBoolean

shadowDeclarations : PathDeclarations [LBool] [LBool]
shadowDeclarations = DeclarePath (shadowTerm Tests.Shadow.linearSource) (LBoolean False) NoPaths

neutralExact : ExactPath {context = [LBool]} {paths = [LBool]} {d = 1}
  (NeutralAt LHere Zero) (NeutralAt LHere One)
neutralExact = PathAbstract (NeutralAt LHere (Var FZ)) Refl Refl

checkedShadowEndpoint : DeclaredEndpoint Tests.Shadow.shadowDeclarations (the (ScopedFace 1) (SEndpoint FZ False))
  (applyExactPath Tests.Shadow.neutralExact (Var FZ)) (Embed (shadowTerm Tests.Shadow.linearSource))
checkedShadowEndpoint = declaredExactApplicationLeft Tests.Shadow.neutralExact (Var FZ) LHere Refl DeclaredHere Refl

substitutedShadowEndpoint : DeclaredEndpoint
  (substitutePathDeclarations Tests.Shadow.replaceBool Tests.Shadow.shadowDeclarations) (the (ScopedFace 1) (SEndpoint FZ False))
  (NeutralAt LHere (Var FZ)) (Embed (LIf (LBoolean True) (LBoolean True) (LBoolean False)))
substitutedShadowEndpoint = substituteDeclaredEndpoint Tests.Shadow.replaceBool Tests.Shadow.checkedShadowEndpoint

-- Weakening through a term binder substitutes the old variable with index 1.
weakenEndpoint : LogicalSubstitution [LBool] [LUnit, LBool]
weakenEndpoint LHere = LRef (LThere LHere)

weakenedShadowEndpoint : DeclaredEndpoint
  (substitutePathDeclarations Tests.Shadow.weakenEndpoint Tests.Shadow.shadowDeclarations) (the (ScopedFace 1) (SEndpoint FZ False))
  (NeutralAt LHere (Var FZ)) (Embed (LIf (LRef (LThere LHere)) (LBoolean True) (LBoolean False)))
weakenedShadowEndpoint = substituteDeclaredEndpoint Tests.Shadow.weakenEndpoint Tests.Shadow.checkedShadowEndpoint

-- Interval preflight rejects an over-budget chain before endpoint extraction.
longReverse : Nat -> ScopedInterval 1
longReverse Z = Var FZ
longReverse (S n) = Reverse (Tests.Shadow.longReverse n)

longReverseExhausts : intervalNodes 12 (Tests.Shadow.longReverse 32) = Nothing
longReverseExhausts = Refl

longReverseEndpointRejected : boundedEndpointEntails SBottom (Tests.Shadow.longReverse 32) False = False
longReverseEndpointRejected = Refl

falseFaceNotEntailed : boundedEndpointEntails {d = 1} STop (Var FZ) False = False
falseFaceNotEntailed = Refl

endpointFaceAccepted : boundedEndpointEntails (the (ScopedFace 1) (SEndpoint FZ False)) (Var FZ) False = True
endpointFaceAccepted = Refl

oppositeFaceRejected : boundedEndpointEntails (the (ScopedFace 1) (SEndpoint FZ True)) (Var FZ) False = False
oppositeFaceRejected = Refl

-- A genuinely nonconstant abstraction uses the declared neutral boundary,
-- not literal equality of its body with either endpoint.
shadowNeutralPath : DeclaredShadowPath Tests.Shadow.shadowDeclarations (the (ScopedFace 0) STop)
  (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (LBoolean False))
shadowNeutralPath = ShadowAbstract (NeutralAt LHere (Var FZ))
  (BodyEndpoint (DeclaredLeft DeclaredHere Refl))
  (BodyEndpoint (DeclaredRight DeclaredHere Refl))

shadowNeutralApplication : applyDeclaredShadowPath Tests.Shadow.shadowNeutralPath Zero = NeutralAt LHere Zero
shadowNeutralApplication = Refl

shadowNeutralApplicationBoundary : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 0) STop)
  (applyDeclaredShadowPath Tests.Shadow.shadowNeutralPath Zero) (Embed (shadowTerm Tests.Shadow.linearSource))
shadowNeutralApplicationBoundary = BodyEndpoint (DeclaredLeft DeclaredHere Refl)

substitutedShadowPath : DeclaredShadowPath
  (substitutePathDeclarations Tests.Shadow.replaceBool Tests.Shadow.shadowDeclarations) (the (ScopedFace 0) STop)
  (Embed (LIf (LBoolean True) (LBoolean True) (LBoolean False))) (Embed (LBoolean False))
substitutedShadowPath = substituteDeclaredShadowPath Tests.Shadow.replaceBool Tests.Shadow.shadowNeutralPath

constantShadowPath : DeclaredShadowPath Tests.Shadow.shadowDeclarations (the (ScopedFace 0) STop)
  (Embed (LBoolean True)) (Embed (LBoolean True))
constantShadowPath = ShadowAbstract (Embed (LBoolean True)) BodyRefl BodyRefl

dimensionMappedEndpoint : DeclaredEndpoint Tests.Shadow.shadowDeclarations
  (the (ScopedFace 0) (substituteScopedFace (atDimension Zero) (SEndpoint FZ False)))
  (NeutralAt LHere Zero) (Embed (shadowTerm Tests.Shadow.linearSource))
dimensionMappedEndpoint = mapDeclaredLeftDimensions {face = SEndpoint FZ False} {i = Var FZ} (atDimension Zero) DeclaredHere Refl

-- Exercise the declarative rules on a genuinely non-reflexive endpoint.
bodyEndpointEqual : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 1) (SEndpoint FZ False))
  (NeutralAt LHere (Var FZ)) (Embed (shadowTerm Tests.Shadow.linearSource))
bodyEndpointEqual = BodyEndpoint (DeclaredLeft DeclaredHere Refl)

bodySymEndpoint : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 1) (SEndpoint FZ False))
  (Embed (shadowTerm Tests.Shadow.linearSource)) (NeutralAt LHere (Var FZ))
bodySymEndpoint = BodySym Tests.Shadow.bodyEndpointEqual

bodyTransEndpoint : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 1) (SEndpoint FZ False))
  (NeutralAt LHere (Var FZ)) (NeutralAt LHere (Var FZ))
bodyTransEndpoint = BodyTrans Tests.Shadow.bodyEndpointEqual Tests.Shadow.bodySymEndpoint

bodyAppCongruence : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 1) (SEndpoint FZ False))
  (BodyApp (BodyLam (Embed (LRef LHere))) (NeutralAt LHere (Var FZ)))
  (BodyApp (BodyLam (Embed (LRef LHere))) (Embed (shadowTerm Tests.Shadow.linearSource)))
bodyAppCongruence = BodyAppEqual BodyRefl Tests.Shadow.bodyEndpointEqual

bodyIfCongruence : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 1) (SEndpoint FZ False))
  (BodyIf (NeutralAt LHere (Var FZ)) (NeutralAt LHere (Var FZ)) (Embed (LBoolean False)))
  (BodyIf (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (LBoolean False)))
bodyIfCongruence = BodyIfEqual Tests.Shadow.bodyEndpointEqual Tests.Shadow.bodyEndpointEqual BodyRefl

bodyUnitElimCongruence : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 1) (SEndpoint FZ False))
  (BodyUnitElim (Embed LUnitValue) (NeutralAt LHere (Var FZ)))
  (BodyUnitElim (Embed LUnitValue) (Embed (shadowTerm Tests.Shadow.linearSource)))
bodyUnitElimCongruence = BodyUnitElimEqual BodyRefl Tests.Shadow.bodyEndpointEqual

shadowApplicationSubstitution :
  applyDeclaredShadowPath (substituteDeclaredShadowPath Tests.Shadow.replaceBool Tests.Shadow.shadowNeutralPath) Zero =
    mapPathTerms Tests.Shadow.replaceBool (applyDeclaredShadowPath Tests.Shadow.shadowNeutralPath Zero)
shadowApplicationSubstitution = substituteDeclaredShadowApplication Tests.Shadow.replaceBool Tests.Shadow.shadowNeutralPath Zero

-- The ambient i=0 constraint shifts to index 1 below the new path binder.
ambientFaceShadowPath : DeclaredShadowPath Tests.Shadow.shadowDeclarations (the (ScopedFace 1) (SEndpoint FZ False))
  (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (shadowTerm Tests.Shadow.linearSource))
ambientFaceShadowPath = ShadowAbstract (NeutralAt LHere (Var (FS FZ)))
  (BodyEndpoint (DeclaredLeft DeclaredHere Refl))
  (BodyEndpoint (DeclaredLeft DeclaredHere Refl))

-- Recertify only the endpoint checks actually used, directly at the ambient face.
genericNeutralZero : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 0) STop)
  (applyDeclaredShadowPath Tests.Shadow.shadowNeutralPath Zero) (Embed (shadowTerm Tests.Shadow.linearSource))
genericNeutralZero = declaredShadowAtZero {left = Embed (shadowTerm Tests.Shadow.linearSource)} {right = Embed (LBoolean False)} (NeutralAt LHere (Var FZ))
  (BodyEndpoint (DeclaredLeft DeclaredHere Refl))
  (BodyEndpoint (DeclaredRight DeclaredHere Refl)) (DimLeft Refl)

genericNeutralOne : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 0) STop)
  (applyDeclaredShadowPath Tests.Shadow.shadowNeutralPath One) (Embed (LBoolean False))
genericNeutralOne = declaredShadowAtOne {left = Embed (shadowTerm Tests.Shadow.linearSource)} {right = Embed (LBoolean False)} (NeutralAt LHere (Var FZ))
  (BodyEndpoint (DeclaredLeft DeclaredHere Refl))
  (BodyEndpoint (DeclaredRight DeclaredHere Refl)) (DimRight Refl)

genericAmbientZero : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 1) (SEndpoint FZ False))
  (applyDeclaredShadowPath Tests.Shadow.ambientFaceShadowPath Zero) (Embed (shadowTerm Tests.Shadow.linearSource))
genericAmbientZero = declaredShadowAtZero {left = Embed (shadowTerm Tests.Shadow.linearSource)} {right = Embed (shadowTerm Tests.Shadow.linearSource)} (NeutralAt LHere (Var (FS FZ)))
  (BodyEndpoint (DeclaredLeft DeclaredHere Refl))
  (BodyEndpoint (DeclaredLeft DeclaredHere Refl)) (DimLeft Refl)

largeDimension : ScopedInterval 0
largeDimension = Reverse (Reverse (Reverse (Reverse (Reverse (Reverse (Reverse (Reverse (Reverse (Reverse (Reverse (Reverse Zero)))))))))))

endpointBeforeDimensionSubstitution : boundedEndpointEntails (the (ScopedFace 1) (SEndpoint FZ False)) (Var FZ) False = True
endpointBeforeDimensionSubstitution = Refl

endpointAfterDimensionSubstitution : boundedEndpointEntails
  (substituteScopedFace (atDimension Tests.Shadow.largeDimension) (SEndpoint FZ False))
  (substituteScoped (atDimension Tests.Shadow.largeDimension) (Var FZ)) False = False
endpointAfterDimensionSubstitution = Refl

pathLevelZero : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 0) STop)
  (applyDeclaredShadowPath Tests.Shadow.shadowNeutralPath Zero) (Embed (shadowTerm Tests.Shadow.linearSource))
pathLevelZero = shadowApplicationZero STop (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (LBoolean False))
  Tests.Shadow.shadowNeutralPath (DimLeft Refl)

pathLevelOne : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 0) STop)
  (applyDeclaredShadowPath Tests.Shadow.shadowNeutralPath One) (Embed (LBoolean False))
pathLevelOne = shadowApplicationOne STop (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (LBoolean False))
  Tests.Shadow.shadowNeutralPath (DimRight Refl)

-- Two logical binders, a linear-source shadow and an ambient dimension all
-- survive dimension weakening and both endpoint instantiations.
nestedAmbientBody : PathBody [LBool] [LBool] 1 (LArrow LUnit (LArrow LUnit LBool))
nestedAmbientBody = BodyLam (BodyLam
  (BodyIf (NeutralAt LHere (Reverse (Var FZ)))
    (Embed (renameLogical LThere (renameLogical LThere (shadowTerm Tests.Shadow.linearSource))))
    (Embed (LBoolean False))))

nestedRestoredZero : mapPathDimensions (atDimension Zero)
  (mapPathDimensions (Var . FS) Tests.Shadow.nestedAmbientBody) = Tests.Shadow.nestedAmbientBody
nestedRestoredZero = pathDimensionsRestored Zero Tests.Shadow.nestedAmbientBody

nestedRestoredOne : mapPathDimensions (atDimension One)
  (mapPathDimensions (Var . FS) Tests.Shadow.nestedAmbientBody) = Tests.Shadow.nestedAmbientBody
nestedRestoredOne = pathDimensionsRestored One Tests.Shadow.nestedAmbientBody

nestedAmbientPath : DeclaredShadowPath Tests.Shadow.shadowDeclarations (the (ScopedFace 1) STop)
  Tests.Shadow.nestedAmbientBody Tests.Shadow.nestedAmbientBody
nestedAmbientPath = ShadowAbstract (mapPathDimensions (Var . FS) Tests.Shadow.nestedAmbientBody) BodyRefl BodyRefl

nestedAmbientZero : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 1) STop)
  (applyDeclaredShadowPath Tests.Shadow.nestedAmbientPath Zero) Tests.Shadow.nestedAmbientBody
nestedAmbientZero = shadowApplicationZero STop Tests.Shadow.nestedAmbientBody Tests.Shadow.nestedAmbientBody Tests.Shadow.nestedAmbientPath DimRefl

nestedAmbientOne : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 1) STop)
  (applyDeclaredShadowPath Tests.Shadow.nestedAmbientPath One) Tests.Shadow.nestedAmbientBody
nestedAmbientOne = shadowApplicationOne STop Tests.Shadow.nestedAmbientBody Tests.Shadow.nestedAmbientBody Tests.Shadow.nestedAmbientPath DimRefl

hasRecertification : (Nat, Maybe a) -> Bool
hasRecertification (_, Nothing) = False
hasRecertification (_, Just _) = True

recertifiedWithFuel : Nat -> (Nat, Maybe a) -> Bool
recertifiedWithFuel expected (remaining, Just _) = remaining == expected
recertifiedWithFuel _ (_, Nothing) = False

rejectedWithFuel : Nat -> (Nat, Maybe a) -> Bool
rejectedWithFuel expected (remaining, Nothing) = remaining == expected
rejectedWithFuel _ (_, Just _) = False

hasAutomaticBoundary : Maybe a -> Bool
hasAutomaticBoundary Nothing = False
hasAutomaticBoundary (Just _) = True


restrictedEndpoint : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 1) (SEndpoint FZ False))
  (NeutralAt LHere (Var FZ)) (Embed (shadowTerm Tests.Shadow.linearSource))
restrictedEndpoint = BodyRestrict {source = SEndpoint FZ False} Tests.Shadow.bodyEndpointEqual Refl

nestedRestrictedEndpoint : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 1) (SEndpoint FZ False))
  (NeutralAt LHere (Var FZ)) (Embed (shadowTerm Tests.Shadow.linearSource))
nestedRestrictedEndpoint = BodyRestrict {source = SEndpoint FZ False} Tests.Shadow.restrictedEndpoint Refl

allBranchesEndpoint : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 1) (SEndpoint FZ False))
  (BodyIf (NeutralAt LHere (Var FZ)) (NeutralAt LHere (Var FZ)) (NeutralAt LHere (Var FZ)))
  (BodyIf (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (shadowTerm Tests.Shadow.linearSource)))
allBranchesEndpoint = BodyIfEqual Tests.Shadow.bodyEndpointEqual Tests.Shadow.bodyEndpointEqual Tests.Shadow.bodyEndpointEqual

largeRestriction : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 1) SBottom)
  (Embed (LBoolean True)) (Embed (LBoolean True))
largeRestriction = BodyRestrict {source = SConjunction STop (SConjunction STop STop)} BodyRefl Refl

laterTransEndpoint : BodyEqual Tests.Shadow.shadowDeclarations (the (ScopedFace 1) (SEndpoint FZ False))
  (NeutralAt LHere (Var FZ)) (Embed (shadowTerm Tests.Shadow.linearSource))
laterTransEndpoint = BodyTrans BodyRefl Tests.Shadow.bodyEndpointEqual

largePreflightSource : Nat -> ScopedInterval 2
largePreflightSource Z = Zero
largePreflightSource (S n) = Reverse (largePreflightSource n)

preflightIntervals : List (ScopedInterval 2)
preflightIntervals = [Zero, One, Var FZ, Var (FS FZ), Reverse (Var FZ),
  Meet (Var FZ) (Join (Var FZ) (Var (FS FZ)))]

preflightFaces : List (ScopedFace 2)
preflightFaces = [SBottom, STop, SEndpoint FZ False, SEndpoint (FS FZ) True,
  SConjunction (SEndpoint FZ False) (SDisjunction (SEndpoint FZ True) STop)]

preflightEnv : Vect 2 (ScopedInterval 1)
preflightEnv = [Reverse (Meet (Var FZ) One), Join Zero (Var FZ)]

-- Two vector cells plus three environment nodes plus three source nodes.
inputBoundaryEnv : Vect 2 (ScopedInterval 1)
inputBoundaryEnv = [Zero, Reverse One]

inputBoundaryInterval : ScopedInterval 2
inputBoundaryInterval = Meet (Var FZ) Zero

inputBoundaryFace : ScopedFace 2
inputBoundaryFace = SConjunction (SEndpoint FZ False) SBottom

largerDestinationEnv : Vect 1 (ScopedInterval 2)
largerDestinationEnv = [Var FZ]

intervalPreflightReference : Nat -> ScopedInterval 2 -> Bool
intervalPreflightReference fuel source =
  boundedShadowIntervalPreflight (MkShadowSubstitutionBounds 2 100 fuel) Tests.Shadow.preflightEnv source ==
    intervalNodes fuel (substituteScoped (\i => index i Tests.Shadow.preflightEnv) source)

facePreflightReference : Nat -> ScopedFace 2 -> Bool
facePreflightReference fuel source =
  boundedShadowFacePreflight (MkShadowSubstitutionBounds 2 100 fuel) Tests.Shadow.preflightEnv source ==
    faceNodes fuel (substituteScopedFace (\i => index i Tests.Shadow.preflightEnv) source)

-- Exercise identity-vector construction beyond the hand-written small scopes.
finiteConstantAtScope : (d : Nat) -> Bool
finiteConstantAtScope d =
  let path : DeclaredShadowPath Tests.Shadow.shadowDeclarations (the (ScopedFace d) STop) (Embed (LBoolean False)) (Embed (LBoolean False)) =
        ShadowAbstract (Embed (LBoolean False)) BodyRefl BodyRefl in
  hasAutomaticBoundary (shadowApplicationZeroFinite (MkShadowSubstitutionBounds (S d) (S (S (S (d + d)))) 0) 1 STop (Embed (LBoolean False)) (Embed (LBoolean False)) path) &&
  hasAutomaticBoundary (shadowApplicationOneFinite (MkShadowSubstitutionBounds (S d) (S (S (S (d + d)))) 0) 1 STop (Embed (LBoolean False)) (Embed (LBoolean False)) path) &&
  not (hasAutomaticBoundary (shadowApplicationZeroFinite (MkShadowSubstitutionBounds d (S (S (S (d + d)))) 0) 1 STop (Embed (LBoolean False)) (Embed (LBoolean False)) path))

public export
checks : List (String, Bool)
checks =
  [ ("finite arbitrary scopes", all finiteConstantAtScope (the (List Nat) [0, 1, 2, 8, 32, 100]))
  , ("finite path zero", hasAutomaticBoundary (shadowApplicationZeroFinite (MkShadowSubstitutionBounds 1 4 1) 1 STop (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (LBoolean False)) Tests.Shadow.shadowNeutralPath))
  , ("finite path one", hasAutomaticBoundary (shadowApplicationOneFinite (MkShadowSubstitutionBounds 1 4 1) 1 STop (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (LBoolean False)) Tests.Shadow.shadowNeutralPath))
  , ("finite path zero proof exhaustion", not (hasAutomaticBoundary (shadowApplicationZeroFinite (MkShadowSubstitutionBounds 1 4 1) 0 STop (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (LBoolean False)) Tests.Shadow.shadowNeutralPath)))
  , ("finite path one input exhaustion", not (hasAutomaticBoundary (shadowApplicationOneFinite (MkShadowSubstitutionBounds 1 3 1) 1 STop (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (LBoolean False)) Tests.Shadow.shadowNeutralPath)))
  , ("finite path zero output exhaustion", not (hasAutomaticBoundary (shadowApplicationZeroFinite (MkShadowSubstitutionBounds 1 4 0) 1 STop (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (LBoolean False)) Tests.Shadow.shadowNeutralPath)))
  , ("finite path scope exhaustion", not (hasAutomaticBoundary (shadowApplicationOneFinite (MkShadowSubstitutionBounds 0 100 100) 1 STop (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (LBoolean False)) Tests.Shadow.shadowNeutralPath)))
  , ("finite path ambient zero", hasAutomaticBoundary (shadowApplicationZeroFinite (MkShadowSubstitutionBounds 2 20 20) 1 (SEndpoint FZ False) (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (shadowTerm Tests.Shadow.linearSource)) Tests.Shadow.ambientFaceShadowPath))
  , ("finite path ambient one", hasAutomaticBoundary (shadowApplicationOneFinite (MkShadowSubstitutionBounds 2 20 20) 1 (SEndpoint FZ False) (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (shadowTerm Tests.Shadow.linearSource)) Tests.Shadow.ambientFaceShadowPath))
  , ("finite path ambient scope rejection", not (hasAutomaticBoundary (shadowApplicationZeroFinite (MkShadowSubstitutionBounds 1 20 20) 1 (SEndpoint FZ False) (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (shadowTerm Tests.Shadow.linearSource)) Tests.Shadow.ambientFaceShadowPath)))
  , ("finite endpoint evidence", hasAutomaticBoundary (recertifyFiniteDimensionEvidence {d = 0} (MkShadowSubstitutionBounds 1 10 10) 1 [Zero] STop Tests.Shadow.bodyEndpointEqual))
  , ("finite linear shadow endpoint evidence", hasAutomaticBoundary (recertifyFiniteDimensionEvidence {d = 0} (MkShadowSubstitutionBounds 1 4 1) 1 [Zero] STop Tests.Shadow.bodyEndpointEqual))
  , ("finite nested restrictions output below", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 6 4) 3 [Zero] STop Tests.Shadow.nestedRestrictedEndpoint == Nothing)
  , ("finite nested restrictions output exact", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 6 5) 3 [Zero] STop Tests.Shadow.nestedRestrictedEndpoint == Just (0, 0, 0))
  , ("finite nested restrictions output above", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 6 6) 3 [Zero] STop Tests.Shadow.nestedRestrictedEndpoint == Just (0, 0, 1))
  , ("finite nested restrictions evidence", hasAutomaticBoundary (recertifyFiniteDimensionEvidence {d = 0} (MkShadowSubstitutionBounds 1 6 5) 3 [Zero] STop Tests.Shadow.nestedRestrictedEndpoint))
  , ("finite application later child fuel", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 4 1) 2 [Zero] STop Tests.Shadow.bodyAppCongruence == Nothing)
  , ("finite application later child output", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 4 0) 3 [Zero] STop Tests.Shadow.bodyAppCongruence == Nothing)
  , ("finite application exact", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 4 1) 3 [Zero] STop Tests.Shadow.bodyAppCongruence == Just (0, 0, 0))
  , ("finite application evidence", hasAutomaticBoundary (recertifyFiniteDimensionEvidence {d = 0} (MkShadowSubstitutionBounds 1 4 1) 3 [Zero] STop Tests.Shadow.bodyAppCongruence))
  , ("finite conditional second child output", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 6 1) 4 [Zero] STop Tests.Shadow.allBranchesEndpoint == Nothing)
  , ("finite conditional third child output", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 6 2) 4 [Zero] STop Tests.Shadow.allBranchesEndpoint == Nothing)
  , ("finite conditional third child fuel", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 6 3) 3 [Zero] STop Tests.Shadow.allBranchesEndpoint == Nothing)
  , ("finite conditional exact", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 6 3) 4 [Zero] STop Tests.Shadow.allBranchesEndpoint == Just (0, 0, 0))
  , ("finite conditional evidence", hasAutomaticBoundary (recertifyFiniteDimensionEvidence {d = 0} (MkShadowSubstitutionBounds 1 6 3) 4 [Zero] STop Tests.Shadow.allBranchesEndpoint))
  , ("finite unit elimination later child fuel", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 4 1) 2 [Zero] STop Tests.Shadow.bodyUnitElimCongruence == Nothing)
  , ("finite unit elimination later child input", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 3 1) 3 [Zero] STop Tests.Shadow.bodyUnitElimCongruence == Nothing)
  , ("finite unit elimination exact", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 4 1) 3 [Zero] STop Tests.Shadow.bodyUnitElimCongruence == Just (0, 0, 0))
  , ("finite unit elimination evidence", hasAutomaticBoundary (recertifyFiniteDimensionEvidence {d = 0} (MkShadowSubstitutionBounds 1 4 1) 3 [Zero] STop Tests.Shadow.bodyUnitElimCongruence))
  , ("finite wrong target rejected", not (hasAutomaticBoundary (recertifyFiniteDimensionEvidence {d = 1} (MkShadowSubstitutionBounds 1 10 10) 1 [Var FZ] STop Tests.Shadow.bodyEndpointEqual)))
  , ("finite proof fuel shared", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 20 20) 3 [Zero] STop Tests.Shadow.bodyTransEndpoint == Nothing)
  , ("finite proof exact aggregate", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 5 2) 4 [Zero] STop Tests.Shadow.bodyTransEndpoint == Just (0, 0, 0))
  , ("finite duplicated output rejected", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 20 1) 4 [Zero] STop Tests.Shadow.bodyTransEndpoint == Nothing)
  , ("finite restriction charges both outputs", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 20 2) 2 [Zero] STop Tests.Shadow.restrictedEndpoint == Nothing)
  , ("finite oversized environment rejected", boundedShadowProofPreflight {d = 1} (MkShadowSubstitutionBounds 1 10 100) 1 [Tests.Shadow.longReverse 1000] STop Tests.Shadow.bodyEndpointEqual == Nothing)
  , ("finite target rejected", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 3 100) 1 [Zero] (SConjunction STop STop) Tests.Shadow.bodyEndpointEqual == Nothing)
  , ("finite source scope rejected", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 0 20 20) 1 [Zero] STop Tests.Shadow.bodyEndpointEqual == Nothing)
  , ("finite destination scope rejected", boundedShadowProofPreflight {d = 2} (MkShadowSubstitutionBounds 1 20 20) 1 Tests.Shadow.largerDestinationEnv STop Tests.Shadow.bodyEndpointEqual == Nothing)
  , ("finite restriction source rejected", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 5 20) 2 [Zero] STop Tests.Shadow.largeRestriction == Nothing)
  , ("finite later branch budget rejected", boundedShadowProofPreflight {d = 0} (MkShadowSubstitutionBounds 1 3 20) 3 [Zero] STop Tests.Shadow.laterTransEndpoint == Nothing)
  , ("finite restriction recertified", hasAutomaticBoundary (recertifyFiniteDimensionEvidence {d = 0} (MkShadowSubstitutionBounds 1 20 20) 2 [Zero] STop Tests.Shadow.restrictedEndpoint))
  , ("interval preflight matches substitution corpus", all (\fuel => all (intervalPreflightReference fuel) Tests.Shadow.preflightIntervals) (the (List Nat) [0, 1, 2, 3, 4, 5, 8, 12, 20]))
  , ("face preflight matches substitution corpus", all (\fuel => all (facePreflightReference fuel) Tests.Shadow.preflightFaces) (the (List Nat) [0, 1, 2, 3, 4, 5, 8, 12, 20]))
  , ("unused large environment rejected", boundedShadowIntervalPreflight (MkShadowSubstitutionBounds 2 20 10) [Zero, Tests.Shadow.longReverse 1000] (the (ScopedInterval 2) (Var FZ)) == Nothing)
  , ("duplicate expansion rejected", boundedShadowIntervalPreflight (MkShadowSubstitutionBounds 2 100 7) Tests.Shadow.preflightEnv (Meet (Var FZ) (Var FZ)) == Nothing)
  , ("interval aggregate input one below", boundedShadowIntervalPreflight (MkShadowSubstitutionBounds 2 7 10) Tests.Shadow.inputBoundaryEnv Tests.Shadow.inputBoundaryInterval == Nothing)
  , ("interval aggregate input exact", boundedShadowIntervalPreflight (MkShadowSubstitutionBounds 2 8 10) Tests.Shadow.inputBoundaryEnv Tests.Shadow.inputBoundaryInterval == Just 7)
  , ("interval aggregate input one above", boundedShadowIntervalPreflight (MkShadowSubstitutionBounds 2 9 10) Tests.Shadow.inputBoundaryEnv Tests.Shadow.inputBoundaryInterval == Just 7)
  , ("face aggregate input one below", boundedShadowFacePreflight (MkShadowSubstitutionBounds 2 7 10) Tests.Shadow.inputBoundaryEnv Tests.Shadow.inputBoundaryFace == Nothing)
  , ("face aggregate input exact", boundedShadowFacePreflight (MkShadowSubstitutionBounds 2 8 10) Tests.Shadow.inputBoundaryEnv Tests.Shadow.inputBoundaryFace == Just 7)
  , ("face aggregate input one above", boundedShadowFacePreflight (MkShadowSubstitutionBounds 2 9 10) Tests.Shadow.inputBoundaryEnv Tests.Shadow.inputBoundaryFace == Just 7)
  , ("scope limit rejected", boundedShadowFacePreflight (MkShadowSubstitutionBounds 1 100 100) Tests.Shadow.preflightEnv STop == Nothing)
  , ("interval destination scope alone rejected", boundedShadowIntervalPreflight (MkShadowSubstitutionBounds 1 10 10) Tests.Shadow.largerDestinationEnv (Var FZ) == Nothing)
  , ("interval destination scope admitted at limit", boundedShadowIntervalPreflight (MkShadowSubstitutionBounds 2 10 10) Tests.Shadow.largerDestinationEnv (Var FZ) == Just 9)
  , ("face destination scope alone rejected", boundedShadowFacePreflight (MkShadowSubstitutionBounds 1 10 10) Tests.Shadow.largerDestinationEnv (SEndpoint FZ False) == Nothing)
  , ("face destination scope admitted at limit", boundedShadowFacePreflight (MkShadowSubstitutionBounds 2 10 10) Tests.Shadow.largerDestinationEnv (SEndpoint FZ False) == Just 9)
  , ("large retained source rejected", boundedShadowIntervalPreflight (MkShadowSubstitutionBounds 2 20 100) Tests.Shadow.preflightEnv (Tests.Shadow.largePreflightSource 1000) == Nothing)
  , ("recertify sym/trans", hasRecertification (recertifyDimensionEvidence 4 (atDimension Zero) STop Tests.Shadow.bodyTransEndpoint))
  , ("recertify success remaining fuel", recertifiedWithFuel 5 (recertifyDimensionEvidence 9 (atDimension Zero) STop Tests.Shadow.bodyTransEndpoint))
  , ("recertify failed endpoint remaining fuel", rejectedWithFuel 8 (recertifyDimensionEvidence 9 Var STop Tests.Shadow.bodyEndpointEqual))
  , ("recertify later trans failure remaining fuel", rejectedWithFuel 6 (recertifyDimensionEvidence 9 Var STop Tests.Shadow.laterTransEndpoint))
  , ("recertify later app failure remaining fuel", rejectedWithFuel 6 (recertifyDimensionEvidence 9 Var STop Tests.Shadow.bodyAppCongruence))
  , ("recertify shared fuel", rejectedWithFuel 0 (recertifyDimensionEvidence 3 (atDimension Zero) STop Tests.Shadow.bodyTransEndpoint))
  , ("recertify app", hasRecertification (recertifyDimensionEvidence 3 (atDimension Zero) STop Tests.Shadow.bodyAppCongruence))
  , ("recertify if", hasRecertification (recertifyDimensionEvidence 4 (atDimension Zero) STop Tests.Shadow.bodyIfCongruence))
  , ("recertify unit elimination", hasRecertification (recertifyDimensionEvidence 3 (atDimension Zero) STop Tests.Shadow.bodyUnitElimCongruence))
  , ("recertify wrong face", not (hasRecertification (recertifyDimensionEvidence 1 Var STop Tests.Shadow.bodyEndpointEqual)))
  , ("recertify same index", hasRecertification (recertifyDimensionEvidence 1 Var (SEndpoint FZ False) Tests.Shadow.bodyEndpointEqual))
  , ("recertify huge replacement", not (hasRecertification (recertifyDimensionEvidence 1 (\_ => Tests.Shadow.longReverse 1000) SBottom Tests.Shadow.bodyEndpointEqual)))
  , ("recertify reverse limit", not (hasRecertification (recertifyDimensionEvidence 1 (atDimension Tests.Shadow.largeDimension) SBottom Tests.Shadow.bodyEndpointEqual)))
  , ("recertify restriction", hasRecertification (recertifyDimensionEvidence 2 (atDimension Zero) STop Tests.Shadow.restrictedEndpoint))
  , ("recertify restriction mismatch", not (hasRecertification (recertifyDimensionEvidence 2 Var STop Tests.Shadow.restrictedEndpoint)))
  , ("auto neutral zero", hasAutomaticBoundary (shadowApplicationZeroAuto 1 STop (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (LBoolean False)) Tests.Shadow.shadowNeutralPath))
  , ("auto neutral one", hasAutomaticBoundary (shadowApplicationOneAuto 1 STop (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (LBoolean False)) Tests.Shadow.shadowNeutralPath))
  , ("auto no fuel", not (hasAutomaticBoundary (shadowApplicationZeroAuto 0 STop (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (LBoolean False)) Tests.Shadow.shadowNeutralPath)))
  , ("auto ambient", hasAutomaticBoundary (shadowApplicationOneAuto 1 (SEndpoint FZ False) (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (shadowTerm Tests.Shadow.linearSource)) Tests.Shadow.ambientFaceShadowPath))
  ]

-- This source is genuinely used linearly; the bridge maps its variable
-- position to the target's abstract base, not Boolean semantics.
bridgeSource : Term [BoolTy] BoolTy
bridgeSource = Ref Here

bridgeSourceUses : Uses Tests.Shadow.bridgeSource [Linear]
bridgeSourceUses = UseRef Here

bridgeSourcePath : DeclaredShadowPath
  (DeclarePath (shadowTerm Tests.Shadow.bridgeSource) (shadowTerm Tests.Shadow.bridgeSource) NoPaths)
  (the (ScopedFace 0) STop) (Embed (shadowTerm Tests.Shadow.bridgeSource)) (Embed (shadowTerm Tests.Shadow.bridgeSource))
bridgeSourcePath = ShadowAbstract (NeutralAt LHere (Var FZ))
  (BodyEndpoint (DeclaredLeft DeclaredHere Refl))
  (BodyEndpoint (DeclaredRight DeclaredHere Refl))

bridgeSourceTyped : NeutralHasType (bridgeContext {context = [LBool]} LHere LHere) (the (ScopedFace 0) STop)
  (NAbstract (NApply (NPath FZ) (Var FZ)))
  (NPathType NType (NBase FZ) (NBase FZ))
bridgeSourceTyped = bridgeDeclaredPath LHere LHere (the (ScopedFace 0) STop)
  {path = Tests.Shadow.bridgeSourcePath} (WitnessNeutral Refl Refl)

bridgeSourceLeft : NeutralEqual (bridgeContext {context = [LBool]} LHere LHere) (the (ScopedFace 1) (SEndpoint FZ False))
  (NApply (NPath FZ) (Var FZ)) (NBase FZ) NType
bridgeSourceLeft = bridgeLeft {context = [LBool]} LHere LHere (the (ScopedFace 1) (SEndpoint FZ False)) (Var FZ)
  (DeclaredLeft DeclaredHere Refl) (IsDeclaredLeft Refl)

bridgeSourceRight : NeutralEqual (bridgeContext {context = [LBool]} LHere LHere) (the (ScopedFace 1) (SEndpoint FZ True))
  (NApply (NPath FZ) (Var FZ)) (NBase FZ) NType
bridgeSourceRight = bridgeRight {context = [LBool]} LHere LHere (the (ScopedFace 1) (SEndpoint FZ True)) (Var FZ)
  (DeclaredRight DeclaredHere Refl) (IsDeclaredRight Refl)

-- The generic implication needs no target solver hypothesis.
inferTargetFace : (face : ScopedFace d) -> (i : ScopedInterval d) -> (side : Bool) ->
  boundedEndpointEntails face i side = True ->
  TypedPath.boundedFaceEntails face (scopedEndpoint i side) = True
inferTargetFace = endpointEntailsFace

longReverseCannotSupplyEndpoint :
  boundedEndpointEntails SBottom (Tests.Shadow.longReverse 32) False = True -> Void
longReverseCannotSupplyEndpoint Refl impossible

-- Equal endpoints still permit the right constructor at the right face.
sameEndpointRight : NeutralEqual (bridgeContext {context = [LBool]} LHere LHere)
  (the (ScopedFace 1) (SEndpoint FZ True))
  (NApply (NPath FZ) (Var FZ)) (NBase FZ) NType
sameEndpointRight = bridgeRight {context = [LBool]} LHere LHere _ _
  (DeclaredRight DeclaredHere Refl) (IsDeclaredRight Refl)

bridgeNonzeroPath : DeclaredShadowPath
  (DeclarePath (LRef (LThere LHere)) (LRef LHere) NoPaths)
  (the (ScopedFace 1) (SEndpoint FZ True))
  (Embed (LRef (LThere LHere))) (Embed (LRef LHere))
bridgeNonzeroPath = ShadowAbstract (NeutralAt LHere (Var FZ))
  (BodyEndpoint (DeclaredLeft DeclaredHere Refl))
  (BodyEndpoint (DeclaredRight DeclaredHere Refl))

bridgeNonzeroTyped : NeutralHasType
  (bridgeContext {context = [LBool, LBool]} (LThere LHere) LHere)
  (the (ScopedFace 1) (SEndpoint FZ True))
  (NAbstract (NApply (NPath FZ) (Var FZ)))
  (NPathType NType (NBase (FS FZ)) (NBase FZ))
bridgeNonzeroTyped = bridgeDeclaredPath {context = [LBool, LBool]} (LThere LHere) LHere _
  {path = Tests.Shadow.bridgeNonzeroPath} (WitnessNeutral Refl Refl)
