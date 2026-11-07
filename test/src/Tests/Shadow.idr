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
import Fibril.Cubical.Logical.ShadowCommon
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

commonLinearIf : CommonHasType [LBool]
  (CIf (CVar FZ) (CBool True) (CBool False)) LBool
commonLinearIf = sourceCommonTyped Tests.Shadow.linearSource

linearIdentity : Term [] (Arrow Linear BoolTy BoolTy)
linearIdentity = Lam Linear (Ref Here)

linearIdentityUses : Uses Tests.Shadow.linearIdentity []
linearIdentityUses = UseLam (UseRef Here) Refl

linearIdentityTranslation :
  commonTerm (shadowTerm Tests.Shadow.linearIdentity) = CLam (CVar FZ)
linearIdentityTranslation = Refl

commonLinearIdentity : CommonHasType [] (CLam (CVar FZ)) (LArrow LBool LBool)
commonLinearIdentity = sourceCommonTyped Tests.Shadow.linearIdentity

-- This captured-variable example tests scope and substitution only: its linear
-- binder is unused, so no Uses derivation is claimed for it.
commonBinder : CommonHasType [LBool]
  (CLam (CIf (CVar (FS FZ)) (CBool True) (CBool False))) (LArrow LUnit LBool)
commonBinder = sourceCommonTyped (the (Term [BoolTy] (Arrow Linear UnitTy BoolTy))
  (Lam Linear (If (Ref (There Here)) (Boolean True) (Boolean False))))

commonSubstitutionUnderBinder :
  commonTerm (shadowTerm (substitute Tests.Shadow.sourceReplacement
    (the (Term [BoolTy] (Arrow Linear UnitTy BoolTy))
      (Lam Linear (If (Ref (There Here)) (Boolean True) (Boolean False)))))) =
  commonTerm (substituteLogical (imageSubstitution [BoolTy] Tests.Shadow.sourceReplacement)
    (shadowTerm (the (Term [BoolTy] (Arrow Linear UnitTy BoolTy))
      (Lam Linear (If (Ref (There Here)) (Boolean True) (Boolean False))))))
commonSubstitutionUnderBinder = sourceCommonSubstitution [BoolTy] Tests.Shadow.sourceReplacement
  (the (Term [BoolTy] (Arrow Linear UnitTy BoolTy))
    (Lam Linear (If (Ref (There Here)) (Boolean True) (Boolean False))))

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

-- Restriction is rechecked with the source endpoint solver, then composed with
-- reflexivity; no target judgment is supplied to the bridge.
structuralBoundary : BodyEqual
  (DeclarePath (LRef (LThere LHere)) (LRef LHere) NoPaths)
  (the (ScopedFace 2) (SConjunction (SEndpoint (FS FZ) True) (SEndpoint FZ False)))
  (NeutralAt LHere (Var FZ)) (Embed (LRef (LThere LHere)))
structuralBoundary = BodyTrans
  (BodyRestrict {source = SEndpoint FZ False} (BodyEndpoint (DeclaredLeft DeclaredHere Refl)) Refl) BodyRefl

structuralBoundaryTarget : NeutralEqual
  (bridgeContext {context = [LBool, LBool]} (LThere LHere) LHere)
  (the (ScopedFace 2) (SConjunction (SEndpoint (FS FZ) True) (SEndpoint FZ False)))
  (NApply (NPath FZ) (Var FZ)) (NBase (FS FZ)) NType
structuralBoundaryTarget = bridgeEquality {context = [LBool, LBool]} (LThere LHere) LHere _
  {source = Tests.Shadow.structuralBoundary} (BridgeTransRefl (BridgeRestrictLeft Refl))

structuralPath : NeutralHasType
  (bridgeContext {context = [LBool, LBool]} (LThere LHere) LHere)
  (the (ScopedFace 1) (SEndpoint FZ True))
  (NAbstract (NApply (NPath FZ) (Var FZ)))
  (NPathType NType (NBase (FS FZ)) (NBase FZ))
structuralPath = bridgeAbstract {context = [LBool, LBool]} (LThere LHere) LHere _
  {zero = Tests.Shadow.structuralBoundary}
  {one = BodySym (BodySym (BodyEndpoint (DeclaredRight DeclaredHere Refl)))}
  (BridgeTransRefl (BridgeRestrictLeft Refl)) (BridgeSym (BridgeSym BridgeEndpointRight))

structuralVariableRefl : NeutralEqual (bridgeContext {context = [LBool, LBool]} LHere (LThere LHere))
  (the (ScopedFace 0) STop) (NBase (FS FZ)) (NBase (FS FZ)) NType
structuralVariableRefl = bridgeEquality {context = [LBool, LBool]} LHere (LThere LHere) _
  {source = BodyRefl {x = Embed (LRef (LThere LHere))}} (BridgeRefl (BridgeVariable (LThere LHere)))

structuralNeutralRefl : NeutralEqual (bridgeContext {context = [LBool]} LHere LHere)
  (the (ScopedFace 1) STop) (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)) NType
structuralNeutralRefl = bridgeEquality {context = [LBool]} LHere LHere _
  {source = BodyRefl {x = NeutralAt LHere (Var FZ)}} (BridgeRefl (BridgeNeutral {a = LBool} (Var FZ)))

structuralLeftReflTrans : NeutralEqual (bridgeContext {context = [LBool]} LHere LHere)
  (the (ScopedFace 1) (SEndpoint FZ False)) (NApply (NPath FZ) (Var FZ)) (NBase FZ) NType
structuralLeftReflTrans = bridgeEquality {context = [LBool]} LHere LHere _
  {source = BodyTrans BodyRefl (BodyEndpoint (DeclaredLeft DeclaredHere Refl))}
  (BridgeLeftReflTrans BridgeEndpointLeft)

structuralRestrictRefl : NeutralEqual (bridgeContext {context = [LBool]} LHere LHere)
  (the (ScopedFace 1) (SEndpoint FZ False)) (NBase FZ) (NBase FZ) NType
structuralRestrictRefl = bridgeEquality {context = [LBool]} LHere LHere _
  {source = BodyRestrict {source = STop} (BodyRefl {x = Embed (LRef LHere)}) Refl}
  (BridgeRestrictRefl (BridgeVariable LHere))

structuralRestrictRight : NeutralEqual (bridgeContext {context = [LBool]} LHere LHere)
  (the (ScopedFace 2) (SConjunction (SEndpoint (FS FZ) False) (SEndpoint FZ True)))
  (NApply (NPath FZ) (Var FZ)) (NBase FZ) NType
structuralRestrictRight = bridgeEquality {context = [LBool]} LHere LHere _
  {source = BodyRestrict {source = SEndpoint FZ True} (BodyEndpoint (DeclaredRight DeclaredHere Refl)) Refl}
  (BridgeRestrictRight Refl)

linearStructuralZero : BodyEqual
  (DeclarePath (shadowTerm Tests.Shadow.bridgeSource) (shadowTerm Tests.Shadow.bridgeSource) NoPaths)
  (the (ScopedFace 1) (SConjunction STop (SEndpoint FZ False)))
  (NeutralAt LHere (Var FZ)) (Embed (shadowTerm Tests.Shadow.bridgeSource))
linearStructuralZero = BodyTrans BodyRefl (BodyEndpoint (DeclaredLeft DeclaredHere Refl))

linearStructuralOne : BodyEqual
  (DeclarePath (shadowTerm Tests.Shadow.bridgeSource) (shadowTerm Tests.Shadow.bridgeSource) NoPaths)
  (the (ScopedFace 1) (SConjunction STop (SEndpoint FZ True)))
  (NeutralAt LHere (Var FZ)) (Embed (shadowTerm Tests.Shadow.bridgeSource))
linearStructuralOne = BodyEndpoint (DeclaredRight DeclaredHere Refl)

linearStructuralShadow : DeclaredShadowPath
  (DeclarePath (shadowTerm Tests.Shadow.bridgeSource) (shadowTerm Tests.Shadow.bridgeSource) NoPaths)
  (the (ScopedFace 0) STop) (Embed (shadowTerm Tests.Shadow.bridgeSource)) (Embed (shadowTerm Tests.Shadow.bridgeSource))
linearStructuralShadow = ShadowAbstract (NeutralAt LHere (Var FZ)) Tests.Shadow.linearStructuralZero Tests.Shadow.linearStructuralOne

linearStructuralTyped : NeutralHasType (bridgeContext {context = [LBool]} LHere LHere) (the (ScopedFace 0) STop)
  (NAbstract (NApply (NPath FZ) (Var FZ))) (NPathType NType (NBase FZ) (NBase FZ))
linearStructuralTyped = bridgeAbstract {context = [LBool]} LHere LHere STop
  {zero = Tests.Shadow.linearStructuralZero} {one = Tests.Shadow.linearStructuralOne}
  (BridgeLeftReflTrans BridgeEndpointLeft) BridgeEndpointRight

-- Both transitivity premises are non-reflexive. The declared endpoints differ.
closureRoundTrip : BodyEqual
  (DeclarePath (LRef (LThere LHere)) (LRef LHere) NoPaths)
  (the (ScopedFace 1) (SEndpoint FZ False))
  (NeutralAt LHere (Var FZ)) (NeutralAt LHere (Var FZ))
closureRoundTrip = BodyTrans (BodyEndpoint (DeclaredLeft DeclaredHere Refl))
  (BodySym (BodyEndpoint (DeclaredLeft DeclaredHere Refl)))

closureRestricted : NeutralEqual
  (bridgeContext {context = [LBool, LBool]} (LThere LHere) LHere)
  (the (ScopedFace 2) (SConjunction (SEndpoint (FS FZ) True) (SEndpoint FZ False)))
  (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)) NType
closureRestricted = bridgeEquality {context = [LBool, LBool]} (LThere LHere) LHere _
  {source = BodyRestrict {source = SEndpoint FZ False}
    (BodyTrans (BodyEndpoint (DeclaredLeft DeclaredHere Refl))
      (BodySym (BodyEndpoint (DeclaredLeft DeclaredHere Refl)))) Refl}
  (BridgeRestrict (BridgeTrans BridgeEndpointLeft (BridgeSym BridgeEndpointLeft)))

linearClosureZero : BodyEqual
  (DeclarePath (shadowTerm Tests.Shadow.bridgeSource) (shadowTerm Tests.Shadow.bridgeSource) NoPaths)
  (the (ScopedFace 1) (SConjunction STop (SEndpoint FZ False)))
  (NeutralAt LHere (Var FZ)) (Embed (shadowTerm Tests.Shadow.bridgeSource))
linearClosureZero = BodyTrans
  (BodyTrans (BodyEndpoint (DeclaredLeft {i = Var FZ} DeclaredHere Refl))
    (BodySym (BodyEndpoint (DeclaredLeft {i = Var FZ} DeclaredHere Refl))))
  (BodyEndpoint (DeclaredLeft {i = Var FZ} DeclaredHere Refl))

linearClosureShadow : DeclaredShadowPath
  (DeclarePath (shadowTerm Tests.Shadow.bridgeSource) (shadowTerm Tests.Shadow.bridgeSource) NoPaths)
  (the (ScopedFace 0) STop) (Embed (shadowTerm Tests.Shadow.bridgeSource)) (Embed (shadowTerm Tests.Shadow.bridgeSource))
linearClosureShadow = ShadowAbstract (NeutralAt LHere (Var FZ)) Tests.Shadow.linearClosureZero Tests.Shadow.linearStructuralOne

linearClosureTyped : NeutralHasType (bridgeContext {context = [LBool]} LHere LHere) (the (ScopedFace 0) STop)
  (NAbstract (NApply (NPath FZ) (Var FZ))) (NPathType NType (NBase FZ) (NBase FZ))
linearClosureTyped = bridgeAbstract {context = [LBool]} LHere LHere STop
  {zero = Tests.Shadow.linearClosureZero} {one = Tests.Shadow.linearStructuralOne}
  (BridgeTrans (BridgeTrans BridgeEndpointLeft (BridgeSym BridgeEndpointLeft)) BridgeEndpointLeft) BridgeEndpointRight

-- Ordinary If and a path application both survive the common translation.
commonPathLinearIf : CommonPathHasType [LBool] [LBool]
  (the (CommonPathTerm 1 1 1) (CPOrdinary (CIf (CVar FZ) (CBool True) (CBool False)))) LBool
commonPathLinearIf = commonPathTermTyped
  (the (PathBody [LBool] [LBool] 1 LBool) (Embed (shadowTerm Tests.Shadow.linearSource)))

commonPathNonconstantBody : CommonPathHasType [LBool] [LBool]
  (the (CommonPathTerm 1 1 1) (CPAt FZ (Var FZ))) LBool
commonPathNonconstantBody = commonPathTermTyped
  (the (PathBody [LBool] [LBool] 1 LBool) (NeutralAt LHere (Var FZ)))

commonPathBinder : CommonPathHasType [LBool] [LBool]
  (the (CommonPathTerm 1 1 1) (CPLam (CPApp (CPOrdinary (CLam (CVar FZ))) (CPAt FZ (Var FZ))))) (LArrow LUnit LBool)
commonPathBinder = commonPathTermTyped
  (the (PathBody [LBool] [LBool] 1 (LArrow LUnit LBool))
    (BodyLam (BodyApp (Embed (LLam (LRef LHere))) (NeutralAt LHere (Var FZ)))))

commonPathBinderDimensions :
  commonPathTerm (mapPathDimensions (atDimension Zero)
    (the (PathBody [LBool] [LBool] 1 (LArrow LUnit LBool))
      (BodyLam (BodyApp (Embed (LLam (LRef LHere))) (NeutralAt LHere (Var FZ)))))) =
  CPLam (CPApp (CPOrdinary (CLam (CVar FZ))) (CPAt FZ Zero))
commonPathBinderDimensions = commonPathDimensionsCommute (atDimension Zero)
  (the (PathBody [LBool] [LBool] 1 (LArrow LUnit LBool))
    (BodyLam (BodyApp (Embed (LLam (LRef LHere))) (NeutralAt LHere (Var FZ)))))

commonLinearIfEndpoint : CommonFaceEqual
  (commonDeclarations (DeclarePath (shadowTerm Tests.Shadow.linearSource) (shadowTerm Tests.Shadow.linearSource) NoPaths))
  (the (ScopedFace 1) (SEndpoint FZ False))
  (CPAt FZ (Var FZ)) (CPOrdinary (CIf (CVar FZ) (CBool True) (CBool False))) LBool
commonLinearIfEndpoint = commonBodyEqual {decls = DeclarePath (shadowTerm Tests.Shadow.linearSource) (shadowTerm Tests.Shadow.linearSource) NoPaths}
  (BodyEndpoint (DeclaredLeft DeclaredHere Refl))

commonLinearIfCongruence : CommonFaceEqual
  (commonDeclarations (DeclarePath (shadowTerm Tests.Shadow.linearSource) (shadowTerm Tests.Shadow.linearSource) NoPaths))
  (the (ScopedFace 1) (SEndpoint FZ False))
  (CPIf (CPAt FZ (Var FZ)) (CPOrdinary (CBool True)) (CPOrdinary (CBool False)))
  (CPIf (CPOrdinary (CIf (CVar FZ) (CBool True) (CBool False))) (CPOrdinary (CBool True)) (CPOrdinary (CBool False))) LBool
commonLinearIfCongruence = commonBodyEqual {decls = DeclarePath (shadowTerm Tests.Shadow.linearSource) (shadowTerm Tests.Shadow.linearSource) NoPaths}
  (BodyIfEqual (BodyEndpoint (DeclaredLeft DeclaredHere Refl)) (BodyRefl {x = Embed (LBoolean True)}) (BodyRefl {x = Embed (LBoolean False)}))

-- A fresh binder varies even in a nonempty ambient dimension context.
commonLinearAmbientSource : DeclaredShadowPath Tests.Shadow.shadowDeclarations
  (the (ScopedFace 1) (SEndpoint FZ False))
  (Embed (shadowTerm Tests.Shadow.linearSource)) (Embed (LBoolean False))
commonLinearAmbientSource = ShadowAbstract (NeutralAt LHere (Var FZ))
  (BodyEndpoint (DeclaredLeft DeclaredHere Refl))
  (BodyEndpoint (DeclaredRight DeclaredHere Refl))

commonLinearAmbientPath : CommonShadowPath (commonDeclarations Tests.Shadow.shadowDeclarations)
  (the (ScopedFace 1) (SEndpoint FZ False))
  (CPOrdinary (CIf (CVar FZ) (CBool True) (CBool False))) (CPOrdinary (CBool False)) LBool
commonLinearAmbientPath = commonDeclaredShadowPath Tests.Shadow.commonLinearAmbientSource

commonLinearAmbientApplication : applyCommonShadowPath Tests.Shadow.commonLinearAmbientPath (Var FZ) = CPAt FZ (Var FZ)
commonLinearAmbientApplication = Refl

commonLinearAmbientZero : CommonFaceEqual (commonDeclarations Tests.Shadow.shadowDeclarations)
  (the (ScopedFace 1) (SEndpoint FZ False)) (CPAt FZ Zero)
  (CPOrdinary (CIf (CVar FZ) (CBool True) (CBool False))) LBool
commonLinearAmbientZero = commonShadowApplicationZero Tests.Shadow.commonLinearAmbientSource (DimLeft Refl)

commonLinearAmbientOne : CommonFaceEqual (commonDeclarations Tests.Shadow.shadowDeclarations)
  (the (ScopedFace 1) (SEndpoint FZ False)) (CPAt FZ One) (CPOrdinary (CBool False)) LBool
commonLinearAmbientOne = commonShadowApplicationOne Tests.Shadow.commonLinearAmbientSource (DimRight Refl)

-- The paired theorem consumes the real linear conditional derivation and a
-- genuine declared neutral path, using the same source substitution for both.
pairedLinearConditional :
  SubstitutionResult (SubstituteHere (Boolean True)) Tests.Shadow.linearSource [Linear] []
pairedLinearConditional =
  case commonQuantitativeSubstitution [BoolTy] (SubstituteHere (Boolean True))
    Tests.Shadow.linearSource [Linear] Tests.Shadow.linearSourceUses []
    (ReplacementHere UseBoolean) Tests.Shadow.shadowNeutralPath of
      (result, _, _) => result

pairedLinearConditionalCommonType :
  CommonHasType [] (CIf (CBool True) (CBool True) (CBool False)) LBool
pairedLinearConditionalCommonType =
  case commonQuantitativeSubstitution [BoolTy] (SubstituteHere (Boolean True))
    Tests.Shadow.linearSource [Linear] Tests.Shadow.linearSourceUses []
    (ReplacementHere UseBoolean) Tests.Shadow.shadowNeutralPath of
      (_, typed, _) => typed

pairedLinearConditionalCommonPath : CommonShadowPath
  (commonDeclarations (the (PathDeclarations [] [LBool]) (DeclarePath (LIf (LBoolean True) (LBoolean True) (LBoolean False)) (LBoolean False) NoPaths)))
  (the (ScopedFace 0) STop)
  (CPOrdinary (CIf (CBool True) (CBool True) (CBool False)))
  (CPOrdinary (CBool False)) LBool
pairedLinearConditionalCommonPath =
  case commonQuantitativeSubstitution [BoolTy] (SubstituteHere (Boolean True))
    Tests.Shadow.linearSource [Linear] Tests.Shadow.linearSourceUses []
    (ReplacementHere UseBoolean) Tests.Shadow.shadowNeutralPath of
      (_, _, path) => path

pairedConditionalLeftEndpoint :
  CPOrdinary (commonTerm (shadowTerm (substitute (singleSubstitution (SubstituteHere (Boolean True))) Tests.Shadow.linearSource))) =
  commonPathTerm (mapPathTerms (imageSubstitution [BoolTy] (singleSubstitution (SubstituteHere (Boolean True))))
    (the (PathBody [LBool] [LBool] 0 LBool) (Embed (shadowTerm Tests.Shadow.linearSource))))
pairedConditionalLeftEndpoint = Refl

-- The source uses both its captured condition and its local binder once.
commonCapturedSource : Term [BoolTy] (Arrow Linear BoolTy BoolTy)
commonCapturedSource = Lam Linear (If (Ref (There Here)) (Ref Here) (Ref Here))

commonCapturedUses : Uses Tests.Shadow.commonCapturedSource [Linear]
commonCapturedUses = UseLam (UseIf (UseRef (There Here)) (UseRef Here) (UseRef Here)) Refl

commonIdentityImage : Fin 1 -> CommonTerm 1
commonIdentityImage FZ = CVar FZ

commonCapturedSubstitution :
  substituteCommon Tests.Shadow.commonIdentityImage
    (commonTerm (shadowTerm Tests.Shadow.commonCapturedSource)) =
  CLam (CIf (CVar (FS FZ)) (CVar FZ) (CVar FZ))
commonCapturedSubstitution = Refl

commonCapturedResultTyped : CommonHasType [LBool]
  (substituteCommon Tests.Shadow.commonIdentityImage
    (commonTerm (shadowTerm Tests.Shadow.commonCapturedSource))) (LArrow LBool LBool)
commonCapturedResultTyped = CLambdaType (CConditionalType (CVariable (LThere LHere)) (CVariable LHere) (CVariable LHere))

commonPathCapturedSubstitution :
  substituteCommonPath Tests.Shadow.commonIdentityImage
    (the (CommonPathTerm 1 1 1)
      (CPLam (CPIf (CPOrdinary (CVar (FS FZ))) (CPAt FZ (Var FZ)) (CPOrdinary (CVar FZ))))) =
  CPLam (CPIf (CPOrdinary (CVar (FS FZ))) (CPAt FZ (Var FZ)) (CPOrdinary (CVar FZ)))
commonPathCapturedSubstitution = Refl

commonTrueImage : Fin 1 -> CommonTerm 0
commonTrueImage FZ = CBool True

commonActualIfSubstitution :
  substituteCommon Tests.Shadow.commonTrueImage (commonTerm (shadowTerm Tests.Shadow.linearSource)) =
  CIf (CBool True) (CBool True) (CBool False)
commonActualIfSubstitution = Refl

commonActualPathSubstitution :
  substituteCommonPath Tests.Shadow.commonTrueImage
    (commonPathTerm (the (PathBody [LBool] [LBool] 1 LBool)
      (BodyIf (Embed (shadowTerm Tests.Shadow.linearSource)) (NeutralAt LHere (Var FZ)) (Embed (LBoolean False))))) =
  CPIf (CPOrdinary (CIf (CBool True) (CBool True) (CBool False))) (CPAt FZ (Var FZ)) (CPOrdinary (CBool False))
commonActualPathSubstitution = Refl

-- The image's own lambda binds index zero; its free Boolean must cross the
-- surrounding lambda without being captured by either binder.
commonCompoundImage : Fin 1 -> CommonTerm 1
commonCompoundImage FZ = CLam (CIf (CVar FZ) (CVar (FS FZ)) (CBool False))

commonCompoundUnderBinder :
  substituteCommon Tests.Shadow.commonCompoundImage
    (the (CommonTerm 1) (CLam (CApp (CVar (FS FZ)) (CVar FZ)))) =
  CLam (CApp (CLam (CIf (CVar FZ) (CVar (FS (FS FZ))) (CBool False))) (CVar FZ))
commonCompoundUnderBinder = Refl

commonCompoundResultTyped : CommonHasType [LBool]
  (substituteCommon Tests.Shadow.commonCompoundImage
    (the (CommonTerm 1) (CLam (CApp (CVar (FS FZ)) (CVar FZ))))) (LArrow LBool LBool)
commonCompoundResultTyped = CLambdaType (CApplicationType
  (CLambdaType (CConditionalType (CVariable LHere) (CVariable (LThere (LThere LHere))) CBoolType))
  (CVariable LHere))

commonMixedDimensions : Fin 1 -> ScopedInterval 2
commonMixedDimensions FZ = Meet (Var FZ) (Reverse (Var (FS FZ)))

commonMixedBody : CommonPathTerm 1 1 1
commonMixedBody = CPLam (CPApp (CPOrdinary (CVar (FS FZ))) (CPAt FZ (Var FZ)))

commonMixedCompound :
  mapCommonPathDimensions Tests.Shadow.commonMixedDimensions
    (substituteCommonPath Tests.Shadow.commonCompoundImage Tests.Shadow.commonMixedBody) =
  substituteCommonPath Tests.Shadow.commonCompoundImage
    (mapCommonPathDimensions Tests.Shadow.commonMixedDimensions Tests.Shadow.commonMixedBody)
commonMixedCompound = commonPathMixedSubstitution Tests.Shadow.commonCompoundImage
  Tests.Shadow.commonMixedDimensions Tests.Shadow.commonMixedBody

commonMixedCompoundResult :
  mapCommonPathDimensions Tests.Shadow.commonMixedDimensions
    (substituteCommonPath Tests.Shadow.commonCompoundImage Tests.Shadow.commonMixedBody) =
  CPLam (CPApp (CPOrdinary (CLam (CIf (CVar FZ) (CVar (FS (FS FZ))) (CBool False))))
    (CPAt FZ (Meet (Var FZ) (Reverse (Var (FS FZ))))) )
commonMixedCompoundResult = Refl

commonCompoundEnvironment : CommonSubstitutionTyped [LArrow LBool LBool] [LBool] Tests.Shadow.commonCompoundImage
commonCompoundEnvironment LHere = CLambdaType (CConditionalType (CVariable LHere) (CVariable (LThere LHere)) CBoolType)

commonCompoundPreservation : CommonHasType [LBool]
  (substituteCommon Tests.Shadow.commonCompoundImage
    (the (CommonTerm 1) (CLam (CApp (CVar (FS FZ)) (CVar FZ))))) (LArrow LBool LBool)
commonCompoundPreservation = substituteCommonTyped Tests.Shadow.commonCompoundImage
  Tests.Shadow.commonCompoundEnvironment (CLambdaType (CApplicationType (CVariable (LThere LHere)) (CVariable LHere)))

commonTrueEnvironment : CommonSubstitutionTyped [LBool] [] Tests.Shadow.commonTrueImage
commonTrueEnvironment LHere = CBoolType

commonLinearPreservation : CommonHasType []
  (substituteCommon Tests.Shadow.commonTrueImage (commonTerm (shadowTerm Tests.Shadow.linearSource))) LBool
commonLinearPreservation = substituteCommonTyped Tests.Shadow.commonTrueImage Tests.Shadow.commonTrueEnvironment (sourceCommonTyped Tests.Shadow.linearSource)

commonPathCompoundPreservation : CommonPathHasType [LBool] [LBool]
  (substituteCommonPath Tests.Shadow.commonCompoundImage Tests.Shadow.commonMixedBody) (LArrow LBool LBool)
commonPathCompoundPreservation = substituteCommonPathTyped Tests.Shadow.commonCompoundImage Tests.Shadow.commonCompoundEnvironment
  (CPLamType (CPAppType (CPOrdinaryType (CVariable (LThere LHere))) (CPAtType LHere)))

-- The image has its own binder and a free variable; two surrounding binders
-- must both shift that free variable while preserving their local variables.
logicalCompoundImage : LogicalSubstitution [LArrow LBool LBool] [LBool]
logicalCompoundImage LHere = LLam (LIf (LRef LHere) (LRef (LThere LHere)) (LBoolean False))

logicalNestedCapture : LogicalTerm [LArrow LBool LBool] (LArrow LBool (LArrow LBool LBool))
logicalNestedCapture = LLam (LLam (LApp (LRef (LThere (LThere LHere))) (LRef LHere)))

commonNestedCaptureCommutes :
  commonTerm (substituteLogical Tests.Shadow.logicalCompoundImage Tests.Shadow.logicalNestedCapture) =
  substituteCommon Tests.Shadow.commonCompoundImage (commonTerm Tests.Shadow.logicalNestedCapture)
commonNestedCaptureCommutes = commonSubstitutionCommutes Tests.Shadow.logicalCompoundImage Tests.Shadow.commonCompoundImage (\v => case v of LHere => Refl) Tests.Shadow.logicalNestedCapture

commonNestedCaptureResult :
  substituteCommon Tests.Shadow.commonCompoundImage (commonTerm Tests.Shadow.logicalNestedCapture) =
  CLam (CLam (CApp (CLam (CIf (CVar FZ) (CVar (FS (FS (FS FZ)))) (CBool False))) (CVar FZ)))
commonNestedCaptureResult = Refl

logicalNamedPath : PathBody [LArrow LBool LBool] [LBool] 1 (LArrow LBool LBool)
logicalNamedPath = BodyLam (BodyApp (Embed (LRef (LThere LHere))) (NeutralAt LHere (Var FZ)))

commonNamedPathCommutes :
  commonPathTerm (mapPathTerms Tests.Shadow.logicalCompoundImage Tests.Shadow.logicalNamedPath) =
  substituteCommonPath Tests.Shadow.commonCompoundImage (commonPathTerm Tests.Shadow.logicalNamedPath)
commonNamedPathCommutes = commonPathSubstitutionCommutes Tests.Shadow.logicalCompoundImage Tests.Shadow.commonCompoundImage (\v => case v of LHere => Refl) Tests.Shadow.logicalNamedPath

commonImageTypedTest : CommonSubstitutionTyped [LArrow LBool LBool] [LBool]
  (commonImageSubstitution [LArrow LBool LBool] Tests.Shadow.logicalCompoundImage)
commonImageTypedTest = commonImageSubstitutionTyped [LArrow LBool LBool] Tests.Shadow.logicalCompoundImage

commonQuantitativeIndependentTest :
  commonTerm (shadowTerm (substitute (singleSubstitution (SubstituteHere (Boolean True))) Tests.Shadow.linearSource)) =
  substituteCommon (commonImageSubstitution [LBool] (imageSubstitution [BoolTy] (singleSubstitution (SubstituteHere (Boolean True)))))
    (commonTerm (shadowTerm Tests.Shadow.linearSource))
commonQuantitativeIndependentTest =
  snd (sourceIndependentCommonQuantitative [BoolTy] (SubstituteHere (Boolean True)) Tests.Shadow.linearSource
    [Linear] Tests.Shadow.linearSourceUses [] (ReplacementHere UseBoolean))

commonMappedAmbientPath : CommonShadowPath
  (the (CommonDeclarations [] [LBool]) (CommonDeclarePath (CIf (CBool True) (CBool True) (CBool False)) (CBool False)
    (CConditionalType CBoolType CBoolType CBoolType) CBoolType CommonNoPaths))
  (the (ScopedFace 1) (SEndpoint FZ False))
  (CPOrdinary (CIf (CBool True) (CBool True) (CBool False))) (CPOrdinary (CBool False)) LBool
commonMappedAmbientPath = substituteCommonShadowPath Tests.Shadow.commonTrueImage Tests.Shadow.commonTrueEnvironment
  (commonDeclarations Tests.Shadow.shadowDeclarations) Tests.Shadow.commonLinearAmbientPath

commonMappedAmbientApplication : applyCommonShadowPath Tests.Shadow.commonMappedAmbientPath (Var FZ) = CPAt FZ (Var FZ)
commonMappedAmbientApplication = substituteCommonShadowApplication Tests.Shadow.commonTrueImage Tests.Shadow.commonTrueEnvironment
  (commonDeclarations Tests.Shadow.shadowDeclarations) Tests.Shadow.commonLinearAmbientPath (Var FZ)

commonMappedEndpoint : CommonFaceEqual
  (the (CommonDeclarations [] [LBool]) (CommonDeclarePath (CIf (CBool True) (CBool True) (CBool False)) (CIf (CBool True) (CBool True) (CBool False))
    (CConditionalType CBoolType CBoolType CBoolType) (CConditionalType CBoolType CBoolType CBoolType) CommonNoPaths))
  (the (ScopedFace 1) (SEndpoint FZ False)) (CPAt FZ (Var FZ))
  (CPOrdinary (CIf (CBool True) (CBool True) (CBool False))) LBool
commonMappedEndpoint = substituteCommonFaceEqual Tests.Shadow.commonTrueImage Tests.Shadow.commonTrueEnvironment
  (commonDeclarations (DeclarePath (shadowTerm Tests.Shadow.linearSource) (shadowTerm Tests.Shadow.linearSource) NoPaths))
  Tests.Shadow.commonLinearIfEndpoint

commonMappedTransRestrict : CommonFaceEqual
  (the (CommonDeclarations [] [LBool]) (CommonDeclarePath (CIf (CBool True) (CBool True) (CBool False)) (CIf (CBool True) (CBool True) (CBool False))
    (CConditionalType CBoolType CBoolType CBoolType) (CConditionalType CBoolType CBoolType CBoolType) CommonNoPaths))
  (the (ScopedFace 1) (SEndpoint FZ False)) (CPAt FZ (Var FZ)) (CPAt FZ (Var FZ)) LBool
commonMappedTransRestrict = substituteCommonFaceEqual Tests.Shadow.commonTrueImage Tests.Shadow.commonTrueEnvironment
  (commonDeclarations (DeclarePath (shadowTerm Tests.Shadow.linearSource) (shadowTerm Tests.Shadow.linearSource) NoPaths))
  (CommonRestrict (CommonTrans Tests.Shadow.commonLinearIfEndpoint (CommonSym Tests.Shadow.commonLinearIfEndpoint)) Refl)

commonPairedIndependent : SubstitutionResult (SubstituteHere (Boolean True)) Tests.Shadow.linearSource [Linear] []
commonPairedIndependent = case commonQuantitativeIndependentPath [BoolTy] (SubstituteHere (Boolean True))
  Tests.Shadow.linearSource [Linear] Tests.Shadow.linearSourceUses [] (ReplacementHere UseBoolean)
  (commonDeclarations Tests.Shadow.shadowDeclarations) Tests.Shadow.commonLinearAmbientPath of
    (result, _, _) => result

-- Constructed directly in common syntax: the endpoint depends on the ambient
-- dimension, which must move from FZ to FS FZ under the abstraction binder.
commonIndependentAmbientDecls : CommonDeclarations [LBool] [LBool]
commonIndependentAmbientDecls = CommonDeclarePath (CVar FZ) (CBool False)
  (CVariable LHere) CBoolType CommonNoPaths

commonIndependentAmbientPath : CommonShadowPath Tests.Shadow.commonIndependentAmbientDecls
  (the (ScopedFace 1) STop) (CPAt FZ (Var FZ)) (CPAt FZ (Var FZ)) LBool
commonIndependentAmbientPath = CommonAbstract (CPAtType LHere) (CPAtType LHere)
  (CPAt FZ (Var (FS FZ))) (CPAtType LHere)
  (CommonRefl (CPAtType LHere)) (CommonRefl (CPAtType LHere))

commonIndependentMappedPath : CommonShadowPath
  (the (CommonDeclarations [] [LBool])
    (CommonDeclarePath (CBool True) (CBool False) CBoolType CBoolType CommonNoPaths))
  (the (ScopedFace 1) STop) (CPAt FZ (Var FZ)) (CPAt FZ (Var FZ)) LBool
commonIndependentMappedPath = substituteCommonShadowPath Tests.Shadow.commonTrueImage
  Tests.Shadow.commonTrueEnvironment Tests.Shadow.commonIndependentAmbientDecls
  Tests.Shadow.commonIndependentAmbientPath

commonIndependentMappedBoundaries : Tests.Shadow.commonIndependentMappedPath =
  CommonAbstract (CPAtType LHere) (CPAtType LHere)
    (CPAt FZ (Var (FS FZ))) (CPAtType LHere)
    (CommonRefl (CPAtType LHere)) (CommonRefl (CPAtType LHere))
commonIndependentMappedBoundaries = Refl

commonIndependentMappedApplication :
  applyCommonShadowPath Tests.Shadow.commonIndependentMappedPath Zero = CPAt FZ (Var FZ)
commonIndependentMappedApplication = substituteCommonShadowApplication Tests.Shadow.commonTrueImage
  Tests.Shadow.commonTrueEnvironment Tests.Shadow.commonIndependentAmbientDecls
  Tests.Shadow.commonIndependentAmbientPath Zero

-- The endpoint check is sound even when an unrelated dimension is non-Boolean.
commonPairValuation : Fin 2 -> DM
commonPairValuation FZ = (False, False)
commonPairValuation (FS FZ) = (False, True)

commonPairNonBoolean : evalDMVal Tests.Shadow.commonPairValuation (Var (FS FZ)) = (False, True)
commonPairNonBoolean = Refl

commonPairEndpointSound : evalDMVal Tests.Shadow.commonPairValuation (Var FZ) = (False, False)
commonPairEndpointSound = commonBoundedEndpointValSound Tests.Shadow.commonPairValuation
  (SEndpoint FZ False) (Var FZ) False Refl Refl

commonPairUnjustifiedEndpointRejected : boundedEndpointEntails
  (the (ScopedFace 2) (SEndpoint FZ False)) (Var (FS FZ)) False = False
commonPairUnjustifiedEndpointRejected = Refl

commonPairNonBooleanFaceFalse : faceAtVal Tests.Shadow.commonPairValuation (SEndpoint (FS FZ) False) = False
commonPairNonBooleanFaceFalse = Refl

-- The endpoint is the actual nonconstant conditional translated from the
-- linear source, interpreted at both possible ordinary valuations.
firstOrderLinearIf : FirstOrderTerm (sourceCommonTyped Tests.Shadow.linearSource)
firstOrderLinearIf = FOIf (FOVar LHere) (FOBool True) (FOBool False)

firstOrderLinearIfTrue : interpretFirstOrderTerm Tests.Shadow.firstOrderLinearIf (FOCons True FONil) = True
firstOrderLinearIfTrue = Refl

firstOrderLinearIfFalse : interpretFirstOrderTerm Tests.Shadow.firstOrderLinearIf (FOCons False FONil) = False
firstOrderLinearIfFalse = Refl

firstOrderTestPath : FirstOrderEnv [LBool] -> DM -> Bool
firstOrderTestPath (FOCons b FONil) (False, False) = b
firstOrderTestPath (FOCons b FONil) (False, True) = False
firstOrderTestPath (FOCons b FONil) (True, False) = b
firstOrderTestPath (FOCons b FONil) (True, True) = True

firstOrderTestDeclarations : CommonDeclarations [LBool] [LBool]
firstOrderTestDeclarations = CommonDeclarePath
  (commonTerm (shadowTerm Tests.Shadow.linearSource)) (CBool True)
  (sourceCommonTyped Tests.Shadow.linearSource) CBoolType CommonNoPaths

firstOrderTestPaths : FirstOrderPaths [LBool] [LBool]
firstOrderTestPaths = FOPath Tests.Shadow.firstOrderTestPath FONoPaths

firstOrderTestZero : (env : FirstOrderEnv [LBool]) -> Tests.Shadow.firstOrderTestPath env (False, False) = interpretFirstOrderTerm Tests.Shadow.firstOrderLinearIf env
firstOrderTestZero (FOCons False FONil) = Refl
firstOrderTestZero (FOCons True FONil) = Refl

firstOrderTestAdmissible : FirstOrderAdmissible Tests.Shadow.firstOrderTestDeclarations Tests.Shadow.firstOrderTestPaths
firstOrderTestAdmissible = FOAdmissibleCons Tests.Shadow.firstOrderLinearIf (FOBool True)
  Tests.Shadow.firstOrderTestZero
  (\(FOCons b FONil) => Refl) FOAdmissibleNil

firstOrderNonBooleanPath : interpretFirstOrderPath
  (the (FirstOrderPathTerm (CPAtType {ctx = [LBool]} {i = Var (FS FZ)} LHere)) (FOAt LHere (Var (FS FZ))))
  (FOCons True FONil) Tests.Shadow.firstOrderTestPaths Tests.Shadow.commonPairValuation = False
firstOrderNonBooleanPath = Refl

-- At this environment both endpoint values are True, while the non-endpoint
-- pair produces False. This detects an implementation collapsing it to either endpoint.
firstOrderPathBothEndpointsTrue :
  (firstOrderPathLookup LHere Tests.Shadow.firstOrderTestPaths (FOCons True FONil) (False, False) = True,
   firstOrderPathLookup LHere Tests.Shadow.firstOrderTestPaths (FOCons True FONil) (True, True) = True)
firstOrderPathBothEndpointsTrue = (Refl, Refl)

firstOrderSecondPath : FirstOrderEnv [LBool] -> DM -> Bool
firstOrderSecondPath env pair = False

firstOrderTwoDeclarations : CommonDeclarations [LBool] [LBool, LBool]
firstOrderTwoDeclarations = CommonDeclarePath (CBool False) (CBool False)
  CBoolType CBoolType Tests.Shadow.firstOrderTestDeclarations

firstOrderTwoPaths : FirstOrderPaths [LBool] [LBool, LBool]
firstOrderTwoPaths = FOPath Tests.Shadow.firstOrderSecondPath Tests.Shadow.firstOrderTestPaths

firstOrderTwoAdmissible : FirstOrderAdmissible Tests.Shadow.firstOrderTwoDeclarations Tests.Shadow.firstOrderTwoPaths
firstOrderTwoAdmissible = FOAdmissibleCons (FOBool False) (FOBool False)
  (\env => Refl) (\env => Refl) Tests.Shadow.firstOrderTestAdmissible

firstOrderHeadLookup :
  (firstOrderPathLookup LHere Tests.Shadow.firstOrderTwoPaths (FOCons True FONil) (False, False) = False,
   firstOrderPathLookup LHere Tests.Shadow.firstOrderTwoPaths (FOCons True FONil) (True, True) = False)
firstOrderHeadLookup = case firstOrderDeclaredLookup CommonDeclaredHere Tests.Shadow.firstOrderTwoPaths Tests.Shadow.firstOrderTwoAdmissible of
  FOEndpoints (FOBool False) (FOBool False) zero one => (zero (FOCons True FONil), one (FOCons True FONil))

firstOrderTailLookup :
  (firstOrderPathLookup (LThere LHere) Tests.Shadow.firstOrderTwoPaths (FOCons False FONil) (False, False) = False,
   firstOrderPathLookup (LThere LHere) Tests.Shadow.firstOrderTwoPaths (FOCons False FONil) (True, True) = True)
firstOrderTailLookup = case firstOrderDeclaredLookup (CommonDeclaredThere CommonDeclaredHere) Tests.Shadow.firstOrderTwoPaths Tests.Shadow.firstOrderTwoAdmissible of
  FOEndpoints (FOIf (FOVar LHere) (FOBool True) (FOBool False)) (FOBool True) zero one =>
    (zero (FOCons False FONil), one (FOCons False FONil))

firstOrderNonBooleanDiffersFromBothEndpoints :
  (interpretFirstOrderPath
     (the (FirstOrderPathTerm (CPAtType {ctx = [LBool]} {i = Var (FS FZ)} LHere)) (FOAt LHere (Var (FS FZ))))
     (FOCons True FONil) Tests.Shadow.firstOrderTestPaths Tests.Shadow.commonPairValuation ==
     firstOrderPathLookup LHere Tests.Shadow.firstOrderTestPaths (FOCons True FONil) (False, False),
   interpretFirstOrderPath
     (the (FirstOrderPathTerm (CPAtType {ctx = [LBool]} {i = Var (FS FZ)} LHere)) (FOAt LHere (Var (FS FZ))))
     (FOCons True FONil) Tests.Shadow.firstOrderTestPaths Tests.Shadow.commonPairValuation ==
     firstOrderPathLookup LHere Tests.Shadow.firstOrderTestPaths (FOCons True FONil) (True, True)) = (False, False)
firstOrderNonBooleanDiffersFromBothEndpoints = Refl

-- The other dimension is genuinely non-Boolean; endpoint soundness uses the
-- same valuation and the declaration's actual nonconstant conditional.
firstOrderLinearDeclaredLeftAtFace :
  Tests.Shadow.firstOrderTestPath (FOCons False FONil)
    (evalDMVal Tests.Shadow.commonPairValuation (Var FZ)) = False
firstOrderLinearDeclaredLeftAtFace =
  case firstOrderDeclaredLeftAtFace CommonDeclaredHere Tests.Shadow.firstOrderTestPaths
    Tests.Shadow.firstOrderTestAdmissible (FOCons False FONil)
    Tests.Shadow.commonPairValuation (SEndpoint FZ False) (Var FZ) Refl Refl of
      FOLeftAtFace (FOIf (FOVar LHere) (FOBool True) (FOBool False)) endpoint => endpoint

firstOrderRightValuation : Fin 1 -> DM
firstOrderRightValuation _ = (True, True)

firstOrderDeclaredRightBoundary :
  Tests.Shadow.firstOrderTestPath (FOCons False FONil)
    (evalDMVal Tests.Shadow.firstOrderRightValuation (Var FZ)) = True
firstOrderDeclaredRightBoundary =
  case firstOrderDeclaredRightAtFace CommonDeclaredHere Tests.Shadow.firstOrderTestPaths
    Tests.Shadow.firstOrderTestAdmissible (FOCons False FONil)
    Tests.Shadow.firstOrderRightValuation (SEndpoint FZ True) (Var FZ) Refl Refl of
      FORightAtFace (FOBool True) endpoint => endpoint

commonPairRestrictedFace : faceAtVal Tests.Shadow.commonPairValuation (SEndpoint FZ False) = True
commonPairRestrictedFace = commonFaceValEntailsSound Tests.Shadow.commonPairValuation
  (SEndpoint FZ False) (SEndpoint FZ False) Refl Refl

-- Preserve the existing non-Boolean dimension and add a second constrained
-- Boolean dimension, so that the conjunction is strictly stronger.
commonPairExtendedValuation : Fin 3 -> DM
commonPairExtendedValuation FZ = Tests.Shadow.commonPairValuation FZ
commonPairExtendedValuation (FS FZ) = Tests.Shadow.commonPairValuation (FS FZ)
commonPairExtendedValuation (FS (FS FZ)) = (False, False)

commonPairStrictFace : ScopedFace 3
commonPairStrictFace = SConjunction (SEndpoint FZ False) (SEndpoint (FS (FS FZ)) False)

commonPairStrictFaceHolds : faceAtVal Tests.Shadow.commonPairExtendedValuation Tests.Shadow.commonPairStrictFace = True
commonPairStrictFaceHolds = Refl

commonPairStrictRestrictedFace : faceAtVal Tests.Shadow.commonPairExtendedValuation (SEndpoint FZ False) = True
commonPairStrictRestrictedFace = commonFaceValEntailsSound Tests.Shadow.commonPairExtendedValuation
  Tests.Shadow.commonPairStrictFace (SEndpoint FZ False) Refl Tests.Shadow.commonPairStrictFaceHolds

commonPairStrictReverseRejected : boundedFaceEntails (SEndpoint FZ False) Tests.Shadow.commonPairStrictFace = False
commonPairStrictReverseRejected = Refl

commonPairExtendedNonBoolean : Tests.Shadow.commonPairExtendedValuation (FS FZ) = (False, True)
commonPairExtendedNonBoolean = Refl

-- Exercise the original two-dimensional valuation directly as well.
commonPairConjunctionRestrictedFace : faceAtVal Tests.Shadow.commonPairValuation (SEndpoint FZ False) = True
commonPairConjunctionRestrictedFace = commonFaceValEntailsSound Tests.Shadow.commonPairValuation
  (SConjunction (SEndpoint FZ False) STop) (SEndpoint FZ False) Refl Refl

-- Independently constructed typing derivations for the same nested syntax.
coherenceTypingOne : CommonHasType [LBool] (CIf (CVar FZ) (CIf (CVar FZ) (CBool True) (CBool False)) (CBool False)) LBool
coherenceTypingOne = CConditionalType (CVariable LHere)
  (CConditionalType (CVariable LHere) CBoolType CBoolType) CBoolType

coherenceTypingTwo : CommonHasType [LBool] (CIf (CVar FZ) (CIf (CVar FZ) (CBool True) (CBool False)) (CBool False)) LBool
coherenceTypingTwo = CConditionalType (CVariable LHere)
  (CConditionalType (CVariable LHere) CBoolType CBoolType) CBoolType

coherenceWitnessOne : FirstOrderTerm Tests.Shadow.coherenceTypingOne
coherenceWitnessOne = FOIf (FOVar LHere) (FOIf (FOVar LHere) (FOBool True) (FOBool False)) (FOBool False)

coherenceWitnessTwo : FirstOrderTerm Tests.Shadow.coherenceTypingTwo
coherenceWitnessTwo = FOIf (FOVar LHere) (FOIf (FOVar LHere) (FOBool True) (FOBool False)) (FOBool False)

coherenceIndependentTerms : (env : FirstOrderEnv [LBool]) ->
  interpretFirstOrderTerm Tests.Shadow.coherenceWitnessOne env = interpretFirstOrderTerm Tests.Shadow.coherenceWitnessTwo env
coherenceIndependentTerms = firstOrderTermCoherent Tests.Shadow.coherenceWitnessOne Tests.Shadow.coherenceWitnessTwo

coherencePathTypingOne : CommonPathHasType [LBool] [LBool]
  (CPIf (CPAt FZ (Var (FS FZ))) (CPOrdinary (CIf (CVar FZ) (CIf (CVar FZ) (CBool True) (CBool False)) (CBool False))) (CPAt FZ (Var FZ))) LBool
coherencePathTypingOne = CPIfType (CPAtType LHere) (CPOrdinaryType Tests.Shadow.coherenceTypingOne) (CPAtType LHere)

coherencePathTypingTwo : CommonPathHasType [LBool] [LBool]
  (CPIf (CPAt FZ (Var (FS FZ))) (CPOrdinary (CIf (CVar FZ) (CIf (CVar FZ) (CBool True) (CBool False)) (CBool False))) (CPAt FZ (Var FZ))) LBool
coherencePathTypingTwo = CPIfType (CPAtType LHere) (CPOrdinaryType Tests.Shadow.coherenceTypingTwo) (CPAtType LHere)

coherencePathWitnessOne : FirstOrderPathTerm Tests.Shadow.coherencePathTypingOne
coherencePathWitnessOne = FOPathIf (FOAt LHere (Var (FS FZ))) (FOOrdinary Tests.Shadow.coherenceWitnessOne) (FOAt LHere (Var FZ))

coherencePathWitnessTwo : FirstOrderPathTerm Tests.Shadow.coherencePathTypingTwo
coherencePathWitnessTwo = FOPathIf (FOAt LHere (Var (FS FZ))) (FOOrdinary Tests.Shadow.coherenceWitnessTwo) (FOAt LHere (Var FZ))

coherenceIndependentPaths : (env : FirstOrderEnv [LBool]) -> (ps : FirstOrderPaths [LBool] [LBool]) -> (valuation : Fin 2 -> DM) ->
  interpretFirstOrderPath Tests.Shadow.coherencePathWitnessOne env ps valuation = interpretFirstOrderPath Tests.Shadow.coherencePathWitnessTwo env ps valuation
coherenceIndependentPaths = firstOrderPathCoherent Tests.Shadow.coherencePathWitnessOne Tests.Shadow.coherencePathWitnessTwo

coherenceArbitraryDimension : {d : Nat} -> (i : ScopedInterval d) ->
  (env : FirstOrderEnv [LBool]) -> (ps : FirstOrderPaths [LBool] [LBool]) -> (valuation : Fin d -> DM) ->
  interpretFirstOrderPath (the (FirstOrderPathTerm (CPAtType {ctx = [LBool]} {i = i} LHere)) (FOAt LHere i)) env ps valuation =
  interpretFirstOrderPath (the (FirstOrderPathTerm (CPAtType {ctx = [LBool]} {i = i} LHere)) (FOAt LHere i)) env ps valuation
coherenceArbitraryDimension i env ps valuation = firstOrderPathCoherent (FOAt LHere i) (FOAt LHere i) env ps valuation

-- This witness indexes the translated BodyEndpoint derivation itself.
firstOrderLinearFaceWitness : FirstOrderFaceEqual Tests.Shadow.commonLinearIfEndpoint
  (FOAt LHere (Var FZ)) (FOOrdinary Tests.Shadow.firstOrderLinearIf)
firstOrderLinearFaceWitness = FOFaceLeft LHere (Var FZ) Tests.Shadow.firstOrderLinearIf CommonDeclaredHere Refl

firstOrderTestFaceWitness : FirstOrderFaceEqual
  (the (CommonFaceEqual Tests.Shadow.firstOrderTestDeclarations (the (ScopedFace 2) (SEndpoint FZ False))
    (CPAt FZ (Var FZ)) (CPOrdinary (CIf (CVar FZ) (CBool True) (CBool False))) LBool)
    (CommonLeft CommonDeclaredHere Refl))
  (FOAt LHere (Var FZ)) (FOOrdinary Tests.Shadow.firstOrderLinearIf)
firstOrderTestFaceWitness = FOFaceLeft LHere (Var FZ) Tests.Shadow.firstOrderLinearIf CommonDeclaredHere Refl

firstOrderFaceSoundExample : Tests.Shadow.firstOrderTestPath (FOCons False FONil)
  (evalDMVal Tests.Shadow.commonPairValuation (Var FZ)) = False
firstOrderFaceSoundExample = firstOrderFaceEqualSound Tests.Shadow.firstOrderTestFaceWitness
  (FOCons False FONil) Tests.Shadow.firstOrderTestPaths Tests.Shadow.firstOrderTestAdmissible
  Tests.Shadow.commonPairValuation Refl

firstOrderFaceRoundTrip : FirstOrderFaceEqual
  (CommonTrans Tests.Shadow.commonLinearIfEndpoint (CommonSym Tests.Shadow.commonLinearIfEndpoint))
  (FOAt LHere (Var FZ)) (FOAt LHere (Var FZ))
firstOrderFaceRoundTrip = FOFaceTrans Tests.Shadow.firstOrderLinearFaceWitness
  (FOFaceSym Tests.Shadow.firstOrderLinearFaceWitness)

firstOrderFaceRestricted : FirstOrderFaceEqual
  (CommonRestrict {face = SEndpoint FZ False} Tests.Shadow.commonLinearIfEndpoint Refl)
  (FOAt LHere (Var FZ)) (FOOrdinary Tests.Shadow.firstOrderLinearIf)
firstOrderFaceRestricted = FOFaceRestrict (SEndpoint FZ False) (SEndpoint FZ False) Refl
  Tests.Shadow.firstOrderLinearFaceWitness

-- Both endpoints of the translated declaration are the actual linear If.
firstOrderLinearPath : FirstOrderEnv [LBool] -> DM -> Bool
firstOrderLinearPath (FOCons b FONil) (False, False) = b
firstOrderLinearPath (FOCons b FONil) (True, True) = b
firstOrderLinearPath (FOCons b FONil) _ = False

firstOrderLinearPaths : FirstOrderPaths [LBool] [LBool]
firstOrderLinearPaths = FOPath Tests.Shadow.firstOrderLinearPath FONoPaths

firstOrderLinearBoundaryZero : (env : FirstOrderEnv [LBool]) -> Tests.Shadow.firstOrderLinearPath env (False, False) = interpretFirstOrderTerm Tests.Shadow.firstOrderLinearIf env
firstOrderLinearBoundaryZero (FOCons False FONil) = Refl
firstOrderLinearBoundaryZero (FOCons True FONil) = Refl

firstOrderLinearBoundaryOne : (env : FirstOrderEnv [LBool]) -> Tests.Shadow.firstOrderLinearPath env (True, True) = interpretFirstOrderTerm Tests.Shadow.firstOrderLinearIf env
firstOrderLinearBoundaryOne (FOCons False FONil) = Refl
firstOrderLinearBoundaryOne (FOCons True FONil) = Refl

firstOrderLinearAdmissible : FirstOrderAdmissible
  (commonDeclarations (DeclarePath (shadowTerm Tests.Shadow.linearSource) (shadowTerm Tests.Shadow.linearSource) NoPaths))
  Tests.Shadow.firstOrderLinearPaths
firstOrderLinearAdmissible = FOAdmissibleCons Tests.Shadow.firstOrderLinearIf Tests.Shadow.firstOrderLinearIf
  Tests.Shadow.firstOrderLinearBoundaryZero Tests.Shadow.firstOrderLinearBoundaryOne FOAdmissibleNil

-- The source Uses evidence remains separate from this semantic claim.
firstOrderTranslatedLeftSound : Tests.Shadow.firstOrderLinearPath (FOCons True FONil) (False, False) = True
firstOrderTranslatedLeftSound = firstOrderFaceEqualSound Tests.Shadow.firstOrderLinearFaceWitness
  (FOCons True FONil) Tests.Shadow.firstOrderLinearPaths Tests.Shadow.firstOrderLinearAdmissible
  (\_ => (False, False)) Refl

firstOrderFaceReflWitness : FirstOrderFaceEqual
  (the (CommonFaceEqual Tests.Shadow.firstOrderTestDeclarations (the (ScopedFace 2) (SEndpoint FZ False))
    (CPAt FZ (Var (FS FZ))) (CPAt FZ (Var (FS FZ))) LBool)
    (CommonRefl (CPAtType LHere)))
  (FOAt LHere (Var (FS FZ))) (FOAt LHere (Var (FS FZ)))
firstOrderFaceReflWitness = FOFaceRefl (FOAt LHere (Var (FS FZ)))

firstOrderFaceReflSound : Tests.Shadow.firstOrderTestPath (FOCons True FONil) (False, True) = False
firstOrderFaceReflSound = trans (firstOrderFaceEqualSound Tests.Shadow.firstOrderFaceReflWitness
  (FOCons True FONil) Tests.Shadow.firstOrderTestPaths Tests.Shadow.firstOrderTestAdmissible
  Tests.Shadow.commonPairValuation Refl) Refl

firstOrderFaceSymSound : True = Tests.Shadow.firstOrderLinearPath (FOCons True FONil) (False, False)
firstOrderFaceSymSound = firstOrderFaceEqualSound (FOFaceSym Tests.Shadow.firstOrderLinearFaceWitness)
  (FOCons True FONil) Tests.Shadow.firstOrderLinearPaths Tests.Shadow.firstOrderLinearAdmissible
  (\_ => (False, False)) Refl

firstOrderFaceTransSound : Tests.Shadow.firstOrderLinearPath (FOCons True FONil) (False, False) = True
firstOrderFaceTransSound = trans (firstOrderFaceEqualSound Tests.Shadow.firstOrderFaceRoundTrip
  (FOCons True FONil) Tests.Shadow.firstOrderLinearPaths Tests.Shadow.firstOrderLinearAdmissible
  (\_ => (False, False)) Refl) Refl

firstOrderThreeDimLeft : FirstOrderFaceEqual
  (the (CommonFaceEqual Tests.Shadow.firstOrderTestDeclarations (the (ScopedFace 3) (SEndpoint FZ False))
    (CPAt FZ (Var FZ)) (CPOrdinary (CIf (CVar FZ) (CBool True) (CBool False))) LBool)
    (CommonLeft CommonDeclaredHere Refl))
  (FOAt LHere (Var FZ)) (FOOrdinary Tests.Shadow.firstOrderLinearIf)
firstOrderThreeDimLeft = FOFaceLeft LHere (Var FZ) Tests.Shadow.firstOrderLinearIf CommonDeclaredHere Refl

firstOrderStrictRestricted : FirstOrderFaceEqual
  (CommonRestrict {face = Tests.Shadow.commonPairStrictFace}
    (the (CommonFaceEqual Tests.Shadow.firstOrderTestDeclarations (the (ScopedFace 3) (SEndpoint FZ False))
      (CPAt FZ (Var FZ)) (CPOrdinary (CIf (CVar FZ) (CBool True) (CBool False))) LBool)
      (CommonLeft CommonDeclaredHere Refl)) Refl)
  (FOAt LHere (Var FZ)) (FOOrdinary Tests.Shadow.firstOrderLinearIf)
firstOrderStrictRestricted = FOFaceRestrict Tests.Shadow.commonPairStrictFace (SEndpoint FZ False) Refl
  Tests.Shadow.firstOrderThreeDimLeft

firstOrderStrictRestrictedSound : Tests.Shadow.firstOrderTestPath (FOCons False FONil) (False, False) = False
firstOrderStrictRestrictedSound = firstOrderFaceEqualSound Tests.Shadow.firstOrderStrictRestricted
  (FOCons False FONil) Tests.Shadow.firstOrderTestPaths Tests.Shadow.firstOrderTestAdmissible
  Tests.Shadow.commonPairExtendedValuation Tests.Shadow.commonPairStrictFaceHolds

firstOrderTailRightWitness : FirstOrderFaceEqual
  (the (CommonFaceEqual Tests.Shadow.firstOrderTwoDeclarations (the (ScopedFace 1) (SEndpoint FZ True))
    (CPAt (FS FZ) (Var FZ)) (CPOrdinary (CBool True)) LBool)
    (CommonRight (CommonDeclaredThere CommonDeclaredHere) Refl))
  (FOAt (LThere LHere) (Var FZ)) (FOOrdinary (FOBool True))
firstOrderTailRightWitness = FOFaceRight (LThere LHere) (Var FZ) (FOBool True)
  (CommonDeclaredThere CommonDeclaredHere) Refl

firstOrderTailRightSound : Tests.Shadow.firstOrderTestPath (FOCons False FONil) (True, True) = True
firstOrderTailRightSound = firstOrderFaceEqualSound Tests.Shadow.firstOrderTailRightWitness
  (FOCons False FONil) Tests.Shadow.firstOrderTwoPaths Tests.Shadow.firstOrderTwoAdmissible
  Tests.Shadow.firstOrderRightValuation Refl

firstOrderTailLeftWitness : FirstOrderFaceEqual
  (the (CommonFaceEqual Tests.Shadow.firstOrderTwoDeclarations (the (ScopedFace 2) (SEndpoint FZ False))
    (CPAt (FS FZ) (Var FZ)) (CPOrdinary (CIf (CVar FZ) (CBool True) (CBool False))) LBool)
    (CommonLeft (CommonDeclaredThere CommonDeclaredHere) Refl))
  (FOAt (LThere LHere) (Var FZ)) (FOOrdinary Tests.Shadow.firstOrderLinearIf)
firstOrderTailLeftWitness = FOFaceLeft (LThere LHere) (Var FZ) Tests.Shadow.firstOrderLinearIf
  (CommonDeclaredThere CommonDeclaredHere) Refl

firstOrderTailLeftSound : Tests.Shadow.firstOrderTestPath (FOCons True FONil) (False, False) = True
firstOrderTailLeftSound = firstOrderFaceEqualSound Tests.Shadow.firstOrderTailLeftWitness
  (FOCons True FONil) Tests.Shadow.firstOrderTwoPaths Tests.Shadow.firstOrderTwoAdmissible
  Tests.Shadow.commonPairValuation Refl

-- Conditional congruence uses the translated linear endpoint in its then branch
-- and a path at the non-Boolean second dimension in its else branch.
firstOrderIfCongruence : FirstOrderFaceEqual
  (CommonIfEqual
    (the (CommonFaceEqual Tests.Shadow.firstOrderTestDeclarations (the (ScopedFace 2) (SEndpoint FZ False))
      (CPOrdinary (CVar FZ)) (CPOrdinary (CVar FZ)) LBool)
      (CommonRefl (CPOrdinaryType (CVariable LHere))))
    (the (CommonFaceEqual Tests.Shadow.firstOrderTestDeclarations (the (ScopedFace 2) (SEndpoint FZ False))
      (CPAt FZ (Var FZ)) (CPOrdinary (CIf (CVar FZ) (CBool True) (CBool False))) LBool)
      (CommonLeft CommonDeclaredHere Refl))
    (CommonRefl (CPAtType {i = Var (FS FZ)} LHere)))
  (FOPathIf (FOOrdinary (FOVar LHere)) (FOAt LHere (Var FZ)) (FOAt LHere (Var (FS FZ))))
  (FOPathIf (FOOrdinary (FOVar LHere)) (FOOrdinary Tests.Shadow.firstOrderLinearIf) (FOAt LHere (Var (FS FZ))))
firstOrderIfCongruence = FOFaceIf (FOOrdinary (FOVar LHere)) (FOOrdinary (FOVar LHere))
  (FOAt LHere (Var FZ)) (FOOrdinary Tests.Shadow.firstOrderLinearIf)
  (FOAt LHere (Var (FS FZ))) (FOAt LHere (Var (FS FZ)))
  (FOFaceRefl (FOOrdinary (FOVar LHere))) Tests.Shadow.firstOrderTestFaceWitness
  (FOFaceRefl (FOAt LHere (Var (FS FZ))))

firstOrderIfCongruenceTrue : Tests.Shadow.firstOrderTestPath (FOCons True FONil) (False, False) = True
firstOrderIfCongruenceTrue = firstOrderFaceEqualSound Tests.Shadow.firstOrderIfCongruence
  (FOCons True FONil) Tests.Shadow.firstOrderTestPaths Tests.Shadow.firstOrderTestAdmissible
  Tests.Shadow.commonPairValuation Refl

firstOrderIfCongruenceFalse : Tests.Shadow.firstOrderTestPath (FOCons False FONil) (False, True) =
  Tests.Shadow.firstOrderTestPath (FOCons False FONil) (False, True)
firstOrderIfCongruenceFalse = firstOrderFaceEqualSound Tests.Shadow.firstOrderIfCongruence
  (FOCons False FONil) Tests.Shadow.firstOrderTestPaths Tests.Shadow.firstOrderTestAdmissible
  Tests.Shadow.commonPairValuation Refl

firstOrderUnitCongruence : FirstOrderFaceEqual
  (CommonUnitElimEqual
    (the (CommonFaceEqual Tests.Shadow.firstOrderTestDeclarations (the (ScopedFace 2) (SEndpoint FZ False))
      (CPOrdinary CUnit) (CPOrdinary CUnit) LUnit) (CommonRefl (CPOrdinaryType CUnitType)))
    (the (CommonFaceEqual Tests.Shadow.firstOrderTestDeclarations (the (ScopedFace 2) (SEndpoint FZ False))
      (CPAt FZ (Var FZ)) (CPOrdinary (CIf (CVar FZ) (CBool True) (CBool False))) LBool)
      (CommonLeft CommonDeclaredHere Refl)))
  (FOPathUnitElim (FOOrdinary FOUnit) (FOAt LHere (Var FZ)))
  (FOPathUnitElim (FOOrdinary FOUnit) (FOOrdinary Tests.Shadow.firstOrderLinearIf))
firstOrderUnitCongruence = FOFaceUnitElim (FOOrdinary FOUnit) (FOOrdinary FOUnit)
  (FOAt LHere (Var FZ)) (FOOrdinary Tests.Shadow.firstOrderLinearIf)
  (FOFaceRefl (FOOrdinary FOUnit)) Tests.Shadow.firstOrderTestFaceWitness

firstOrderUnitCongruenceSound : Tests.Shadow.firstOrderTestPath (FOCons True FONil) (False, False) = True
firstOrderUnitCongruenceSound = firstOrderFaceEqualSound Tests.Shadow.firstOrderUnitCongruence
  (FOCons True FONil) Tests.Shadow.firstOrderTestPaths Tests.Shadow.firstOrderTestAdmissible
  Tests.Shadow.commonPairValuation Refl

firstOrderIfRestrictedSound : Tests.Shadow.firstOrderTestPath (FOCons True FONil) (False, False) = True
firstOrderIfRestrictedSound = firstOrderFaceEqualSound
  (FOFaceRestrict (SConjunction (SEndpoint FZ False) STop) (SEndpoint FZ False) Refl Tests.Shadow.firstOrderIfCongruence)
  (FOCons True FONil) Tests.Shadow.firstOrderTestPaths Tests.Shadow.firstOrderTestAdmissible
  Tests.Shadow.commonPairValuation Refl

-- The two implementations are definitionally different functions, but are
-- equal in the arrow setoid without assuming function extensionality.
setoidIdentity : CommonMorphism Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid
setoidIdentity = MkCommonMorphism (\x => x) (\eq => eq)

conditionalBool : Bool -> Bool
conditionalBool False = False
conditionalBool True = True

setoidConditionalIdentity : CommonMorphism Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid
setoidConditionalIdentity = MkCommonMorphism Tests.Shadow.conditionalBool respect
  where
    respect : {x, y : Bool} -> x = y ->
      Tests.Shadow.conditionalBool x = Tests.Shadow.conditionalBool y
    respect {x = False} Refl = Refl
    respect {x = True} Refl = Refl

setoidIdentityEquivalent : morphismsRelated Tests.Shadow.setoidIdentity Tests.Shadow.setoidConditionalIdentity
setoidIdentityEquivalent False False Refl = Refl
setoidIdentityEquivalent True True Refl = Refl

setoidHigherApplication : related Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid
  (applyMorphism Tests.Shadow.setoidIdentity True) (applyMorphism Tests.Shadow.setoidConditionalIdentity True)
setoidHigherApplication = commonApplicationCongruence {a = Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid} {b = Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid} {f = Tests.Shadow.setoidIdentity} {g = Tests.Shadow.setoidConditionalIdentity} Tests.Shadow.setoidIdentityEquivalent Refl

-- An indiscrete domain exposes a function which cannot be made a morphism.
indiscreteBoolSetoid : CommonSetoid
indiscreteBoolSetoid = MkCommonSetoid Bool (\_, _ => Builtin.Unit)
  (\_ => ()) (\_ => ()) (\_, _ => ())

falseNotTrueSetoid : False = True -> Void
falseNotTrueSetoid Refl impossible

identityNotIndiscreteMorphism :
  ({x, y : Bool} -> related Tests.Shadow.indiscreteBoolSetoid x y ->
    related Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid x y) -> Void
identityNotIndiscreteMorphism preserves = falseNotTrueSetoid (preserves {x = False} {y = True} ())

unequalSetoidBools : related Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid False True -> Void
unequalSetoidBools = falseNotTrueSetoid

higherIdentity : CommonMorphism
  (commonArrowSetoid Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid)
  (commonArrowSetoid Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid)
higherIdentity = MkCommonMorphism (\f => f) (\eq => eq)

higherIdentityRelated : morphismsRelated
  (applyMorphism Tests.Shadow.higherIdentity Tests.Shadow.setoidIdentity)
  (applyMorphism Tests.Shadow.higherIdentity Tests.Shadow.setoidConditionalIdentity)
higherIdentityRelated = Tests.Shadow.setoidIdentityEquivalent

-- Interpret a nested logical arrow, rather than constructing only its setoid
-- manually: the carrier is a morphism on Bool-to-Bool morphisms.
nestedLogicalArrowIdentity : carrier (commonTypeSetoid
  (LArrow (LArrow LBool LBool) (LArrow LBool LBool)))
nestedLogicalArrowIdentity = MkCommonMorphism (\f => f) (\fg => fg)

nestedLogicalArrowApplication : morphismsRelated
  (applyMorphism Tests.Shadow.nestedLogicalArrowIdentity Tests.Shadow.setoidIdentity)
  (applyMorphism Tests.Shadow.nestedLogicalArrowIdentity Tests.Shadow.setoidConditionalIdentity)
nestedLogicalArrowApplication = Tests.Shadow.setoidIdentityEquivalent

-- Unlike Bool equality, this domain relates False and True. The two constant
-- maps preserve even that relation, so the heterogeneous arrow rule applies.
indiscreteConstantTrue : CommonMorphism Tests.Shadow.indiscreteBoolSetoid
  Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid
indiscreteConstantTrue = MkCommonMorphism (\_ => True) (\_ => Refl)

indiscreteTrueFunction : Bool -> Bool
indiscreteTrueFunction False = True
indiscreteTrueFunction True = True

indiscreteConditionalTrue : CommonMorphism Tests.Shadow.indiscreteBoolSetoid
  Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid
indiscreteConditionalTrue = MkCommonMorphism Tests.Shadow.indiscreteTrueFunction (\rel => respect rel)
  where
    respect : {x, y : Bool} -> Builtin.Unit ->
      Tests.Shadow.indiscreteTrueFunction x = Tests.Shadow.indiscreteTrueFunction y
    respect {x = False} {y = False} _ = Refl
    respect {x = False} {y = True} _ = Refl
    respect {x = True} {y = False} _ = Refl
    respect {x = True} {y = True} _ = Refl

indiscreteConstantsRelated : morphismsRelated Tests.Shadow.indiscreteConstantTrue
  Tests.Shadow.indiscreteConditionalTrue
indiscreteConstantsRelated False False _ = Refl
indiscreteConstantsRelated False True _ = Refl
indiscreteConstantsRelated True False _ = Refl
indiscreteConstantsRelated True True _ = Refl

indiscreteDistinctApplication :
  applyMorphism Tests.Shadow.indiscreteConstantTrue False =
  applyMorphism Tests.Shadow.indiscreteConditionalTrue True
indiscreteDistinctApplication = commonApplicationCongruence
  {a = Tests.Shadow.indiscreteBoolSetoid}
  {b = Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid}
  {f = Tests.Shadow.indiscreteConstantTrue} {g = Tests.Shadow.indiscreteConditionalTrue}
  {x = False} {y = True} Tests.Shadow.indiscreteConstantsRelated ()

indiscreteConstantsSymmetric : morphismsRelated Tests.Shadow.indiscreteConditionalTrue
  Tests.Shadow.indiscreteConstantTrue
indiscreteConstantsSymmetric = relationSym
  (commonArrowSetoid Tests.Shadow.indiscreteBoolSetoid Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid)
  {x = Tests.Shadow.indiscreteConstantTrue} {y = Tests.Shadow.indiscreteConditionalTrue}
  Tests.Shadow.indiscreteConstantsRelated

indiscreteConstantsTransitive : morphismsRelated Tests.Shadow.indiscreteConstantTrue
  Tests.Shadow.indiscreteConstantTrue
indiscreteConstantsTransitive = relationTrans
  (commonArrowSetoid Tests.Shadow.indiscreteBoolSetoid Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid)
  {x = Tests.Shadow.indiscreteConstantTrue} {y = Tests.Shadow.indiscreteConditionalTrue}
  {z = Tests.Shadow.indiscreteConstantTrue}
  Tests.Shadow.indiscreteConstantsRelated Tests.Shadow.indiscreteConstantsSymmetric

indiscreteTransitiveDistinct :
  applyMorphism Tests.Shadow.indiscreteConstantTrue False =
  applyMorphism Tests.Shadow.indiscreteConstantTrue True
indiscreteTransitiveDistinct = Tests.Shadow.indiscreteConstantsTransitive False True ()

-- The two environments contain different, extensionally related functions.
commonLookupRelatedEnvironments :
  related (commonTypeSetoid (LArrow LBool LBool))
    (applyMorphism (commonEnvironmentLookup [LArrow LBool LBool] (LArrow LBool LBool) LHere)
      (Tests.Shadow.setoidIdentity, ()))
    (applyMorphism (commonEnvironmentLookup [LArrow LBool LBool] (LArrow LBool LBool) LHere)
      (Tests.Shadow.setoidConditionalIdentity, ()))
commonLookupRelatedEnvironments = respectsRelation
  (commonEnvironmentLookup [LArrow LBool LBool] (LArrow LBool LBool) LHere)
  {x = (Tests.Shadow.setoidIdentity, ())} {y = (Tests.Shadow.setoidConditionalIdentity, ())}
  (Tests.Shadow.setoidIdentityEquivalent, Refl)

commonCapturedLookup :
  applyMorphism (commonEnvironmentLookup [LUnit, LBool] LBool (LThere LHere))
    ((), (True, ())) = True
commonCapturedLookup = Refl

commonCurriedCapture :
  applyMorphism (applyMorphism
    (commonCurry {env = commonEnvironmentSetoid [LBool]}
      {a = commonTypeSetoid LUnit} {b = commonTypeSetoid LBool}
      (commonEnvironmentLookup [LUnit, LBool] LBool (LThere LHere)))
    (True, ())) () = True
commonCurriedCapture = Refl

-- Curried bodies can use related, extensionally distinct captured functions,
-- while accepting different values related by the indiscrete input setoid.
curriedCapturedFunctionBody : CommonMorphism
  (commonProductSetoid Tests.Shadow.indiscreteBoolSetoid
    (commonArrowSetoid Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid
      Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid))
  Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid
curriedCapturedFunctionBody = MkCommonMorphism
  (\pair => applyMorphism (snd pair) True)
  (\rel => snd rel True True Refl)

curriedCapturedFunction : CommonMorphism
  (commonArrowSetoid Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid
    Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid)
  (commonArrowSetoid Tests.Shadow.indiscreteBoolSetoid
    Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid)
curriedCapturedFunction = commonCurry Tests.Shadow.curriedCapturedFunctionBody

curriedDistinctEnvironmentsAndInputs :
  applyMorphism (applyMorphism Tests.Shadow.curriedCapturedFunction Tests.Shadow.setoidIdentity) False =
  applyMorphism (applyMorphism Tests.Shadow.curriedCapturedFunction Tests.Shadow.setoidConditionalIdentity) True
curriedDistinctEnvironmentsAndInputs = respectsRelation Tests.Shadow.curriedCapturedFunction
  {x = Tests.Shadow.setoidIdentity} {y = Tests.Shadow.setoidConditionalIdentity}
  Tests.Shadow.setoidIdentityEquivalent False True ()

indiscreteIdentity : CommonMorphism Tests.Shadow.indiscreteBoolSetoid Tests.Shadow.indiscreteBoolSetoid
indiscreteIdentity = MkCommonMorphism (\x => x) (\_ => ())

constantIndiscreteFunction : CommonMorphism Tests.Shadow.indiscreteBoolSetoid
  (commonArrowSetoid Tests.Shadow.indiscreteBoolSetoid
    Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid)
constantIndiscreteFunction = commonConstant Tests.Shadow.indiscreteConstantTrue

constantPreservesDistinctEnvironments :
  applyMorphism (applyMorphism Tests.Shadow.constantIndiscreteFunction False) False =
  applyMorphism (applyMorphism Tests.Shadow.constantIndiscreteFunction True) True
constantPreservesDistinctEnvironments = respectsRelation Tests.Shadow.constantIndiscreteFunction
  {x = False} {y = True} () False True ()

appliedIndiscreteFunction : CommonMorphism Tests.Shadow.indiscreteBoolSetoid
  Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid
appliedIndiscreteFunction = commonApply Tests.Shadow.constantIndiscreteFunction Tests.Shadow.indiscreteIdentity

appliedFunctionPreservesDistinctEnvironments :
  applyMorphism Tests.Shadow.appliedIndiscreteFunction False =
  applyMorphism Tests.Shadow.appliedIndiscreteFunction True
appliedFunctionPreservesDistinctEnvironments = respectsRelation Tests.Shadow.appliedIndiscreteFunction
  {x = False} {y = True} ()

appliedFunctionResult : applyMorphism Tests.Shadow.appliedIndiscreteFunction False = True
appliedFunctionResult = Refl

higherOrderLinearIf : HigherOrderTerm [LBool] LBool (sourceCommonTyped Tests.Shadow.linearSource)
higherOrderLinearIf = HOIf [LBool] LBool (HOVar [LBool] LBool LHere)
  (HOBool [LBool] True) (HOBool [LBool] False)

higherOrderLinearIfAgain : HigherOrderTerm [LBool] LBool (sourceCommonTyped Tests.Shadow.linearSource)
higherOrderLinearIfAgain = HOIf [LBool] LBool (HOVar [LBool] LBool LHere)
  (HOBool [LBool] True) (HOBool [LBool] False)

higherOrderLinearAlignment : HigherOrderAlignment Tests.Shadow.higherOrderLinearIf Tests.Shadow.higherOrderLinearIfAgain
higherOrderLinearAlignment = AlignIf (AlignVar [LBool] LBool LHere) (AlignBool [LBool] True) (AlignBool [LBool] False)

higherOrderLinearTrue : applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderLinearIf) (True, ()) = True
higherOrderLinearTrue = Refl

higherOrderLinearFalse : applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderLinearIf) (False, ()) = False
higherOrderLinearFalse = Refl

higherOrderCapture : HigherOrderTerm [LBool] LBool
  (CApplicationType (CLambdaType (CVariable (LThere LHere))) CUnitType)
higherOrderCapture = HOApplication [LBool] LUnit LBool
  (HOLambda [LBool] LUnit LBool (HOVar [LUnit, LBool] LBool (LThere LHere)))
  (HOUnit [LBool])

higherOrderCaptureAgain : HigherOrderTerm [LBool] LBool
  (CApplicationType (CLambdaType (CVariable (LThere LHere))) CUnitType)
higherOrderCaptureAgain = HOApplication [LBool] LUnit LBool
  (HOLambda [LBool] LUnit LBool (HOVar [LUnit, LBool] LBool (LThere LHere)))
  (HOUnit [LBool])

higherOrderCaptureAlignment : HigherOrderAlignment Tests.Shadow.higherOrderCapture Tests.Shadow.higherOrderCaptureAgain
higherOrderCaptureAlignment = AlignApplication
  (AlignLambda (AlignVar [LUnit, LBool] LBool (LThere LHere))) (AlignUnit [LBool])

higherOrderCaptureResult : applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderCapture) (True, ()) = True
higherOrderCaptureResult = Refl

higherOrderArrowIf : HigherOrderTerm [LBool, LArrow LBool LBool] (LArrow LBool LBool)
  (CConditionalType (CVariable LHere) (CVariable (LThere LHere)) (CVariable (LThere LHere)))
higherOrderArrowIf = HOIf [LBool, LArrow LBool LBool] (LArrow LBool LBool)
  (HOVar [LBool, LArrow LBool LBool] LBool LHere)
  (HOVar [LBool, LArrow LBool LBool] (LArrow LBool LBool) (LThere LHere))
  (HOVar [LBool, LArrow LBool LBool] (LArrow LBool LBool) (LThere LHere))

higherOrderArrowIfRelated :
  related (commonTypeSetoid (LArrow LBool LBool))
    (applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderArrowIf) (True, (Tests.Shadow.setoidIdentity, ())))
    (applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderArrowIf) (True, (Tests.Shadow.setoidConditionalIdentity, ())))
higherOrderArrowIfRelated = respectsRelation (higherOrderTermSemantics Tests.Shadow.higherOrderArrowIf)
  {x = (True, (Tests.Shadow.setoidIdentity, ()))}
  {y = (True, (Tests.Shadow.setoidConditionalIdentity, ()))}
  (Refl, (Tests.Shadow.setoidIdentityEquivalent, Refl))

higherOrderBoolIdentity : HigherOrderTerm [LBool] (LArrow LBool LBool)
  (CLambdaType (CVariable LHere))
higherOrderBoolIdentity = HOLambda [LBool] LBool LBool
  (HOVar [LBool, LBool] LBool LHere)

higherOrderNestedLinear : HigherOrderTerm [LBool] LBool
  (CApplicationType (CLambdaType (CVariable LHere))
    (CApplicationType (CLambdaType (CVariable LHere)) (sourceCommonTyped Tests.Shadow.linearSource)))
higherOrderNestedLinear = HOApplication [LBool] LBool LBool Tests.Shadow.higherOrderBoolIdentity
  (HOApplication [LBool] LBool LBool Tests.Shadow.higherOrderBoolIdentity Tests.Shadow.higherOrderLinearIf)

higherOrderNestedLinearAlignment : HigherOrderAlignment Tests.Shadow.higherOrderNestedLinear Tests.Shadow.higherOrderNestedLinear
higherOrderNestedLinearAlignment = AlignApplication
  (AlignLambda (AlignVar [LBool, LBool] LBool LHere))
  (AlignApplication (AlignLambda (AlignVar [LBool, LBool] LBool LHere))
    Tests.Shadow.higherOrderLinearAlignment)

higherOrderNestedLinearAligned :
  related (commonTypeSetoid LBool)
    (applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderNestedLinear) (True, ()))
    (applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderNestedLinear) (True, ()))
higherOrderNestedLinearAligned = higherOrderAlignedRelated Tests.Shadow.higherOrderNestedLinearAlignment
  (True, ()) (True, ()) (Refl, Refl)

higherOrderArrowIfAlignment : HigherOrderAlignment Tests.Shadow.higherOrderArrowIf Tests.Shadow.higherOrderArrowIf
higherOrderArrowIfAlignment = AlignIf (AlignVar [LBool, LArrow LBool LBool] LBool LHere)
  (AlignVar [LBool, LArrow LBool LBool] (LArrow LBool LBool) (LThere LHere))
  (AlignVar [LBool, LArrow LBool LBool] (LArrow LBool LBool) (LThere LHere))

higherOrderArrowIfAlignedDistinct :
  related (commonTypeSetoid (LArrow LBool LBool))
    (applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderArrowIf) (True, (Tests.Shadow.setoidIdentity, ())))
    (applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderArrowIf) (True, (Tests.Shadow.setoidConditionalIdentity, ())))
higherOrderArrowIfAlignedDistinct = higherOrderAlignedRelated Tests.Shadow.higherOrderArrowIfAlignment
  (True, (Tests.Shadow.setoidIdentity, ())) (True, (Tests.Shadow.setoidConditionalIdentity, ()))
  (Refl, (Tests.Shadow.setoidIdentityEquivalent, Refl))

higherOrderUnitElimAligned :
  related (commonTypeSetoid LBool)
    (applyMorphism (higherOrderTermSemantics (HOUnitElim [LBool] LBool (HOUnit [LBool]) (HOVar [LBool] LBool LHere))) (True, ()))
    (applyMorphism (higherOrderTermSemantics (HOUnitElim [LBool] LBool (HOUnit [LBool]) (HOVar [LBool] LBool LHere))) (True, ()))
higherOrderUnitElimAligned = higherOrderAlignedRelated
  (AlignUnitElim (AlignUnit [LBool]) (AlignVar [LBool] LBool LHere)) (True, ()) (True, ()) (Refl, Refl)

higherOrderNestedLinearBeta :
  higherOrderTermSemantics Tests.Shadow.higherOrderNestedLinear =
    commonApply (higherOrderTermSemantics Tests.Shadow.higherOrderBoolIdentity)
      (higherOrderTermSemantics (HOApplication [LBool] LBool LBool
        Tests.Shadow.higherOrderBoolIdentity Tests.Shadow.higherOrderLinearIf))
higherOrderNestedLinearBeta = higherOrderApplicationBeta Tests.Shadow.higherOrderBoolIdentity
  (HOApplication [LBool] LBool LBool Tests.Shadow.higherOrderBoolIdentity Tests.Shadow.higherOrderLinearIf)

higherOrderNestedLinearResult : applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderNestedLinear) (True, ()) = True
higherOrderNestedLinearResult = trans
  (higherOrderApplicationBetaAt Tests.Shadow.higherOrderBoolIdentity
    (HOApplication [LBool] LBool LBool Tests.Shadow.higherOrderBoolIdentity Tests.Shadow.higherOrderLinearIf) (True, ())) Refl

-- The Unit and arrow-result cases exercise the other branches of the generic
-- application law in an open Boolean environment.
higherOrderUnitFunction : HigherOrderTerm [LBool] (LArrow LBool LUnit)
  (CLambdaType CUnitType)
higherOrderUnitFunction = HOLambda [LBool] LBool LUnit (HOUnit [LBool, LBool])

higherOrderUnitArgument : HigherOrderTerm [LBool] LBool (CVariable LHere)
higherOrderUnitArgument = HOVar [LBool] LBool LHere

higherOrderUnitApplication : HigherOrderTerm [LBool] LUnit
  (CApplicationType (CLambdaType CUnitType) (CVariable LHere))
higherOrderUnitApplication = HOApplication [LBool] LBool LUnit
  Tests.Shadow.higherOrderUnitFunction Tests.Shadow.higherOrderUnitArgument

higherOrderUnitApplicationBeta :
  higherOrderTermSemantics Tests.Shadow.higherOrderUnitApplication =
    commonApply (higherOrderTermSemantics Tests.Shadow.higherOrderUnitFunction)
      (higherOrderTermSemantics Tests.Shadow.higherOrderUnitArgument)
higherOrderUnitApplicationBeta = higherOrderApplicationBeta
  Tests.Shadow.higherOrderUnitFunction Tests.Shadow.higherOrderUnitArgument

higherOrderUnitApplicationResult :
  applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderUnitApplication) (True, ()) = ()
higherOrderUnitApplicationResult = trans
  (cong (\m => applyMorphism m (True, ())) Tests.Shadow.higherOrderUnitApplicationBeta) Refl

higherOrderUnitApplicationPointwiseResult :
  applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderUnitApplication) (False, ()) = ()
higherOrderUnitApplicationPointwiseResult = trans
  (higherOrderApplicationBetaAt Tests.Shadow.higherOrderUnitFunction
    Tests.Shadow.higherOrderUnitArgument (False, ())) Refl

higherOrderArrowFunction : HigherOrderTerm [LBool] (LArrow LBool (LArrow LBool LBool))
  (CLambdaType (CLambdaType (CVariable (LThere LHere))))
higherOrderArrowFunction = HOLambda [LBool] LBool (LArrow LBool LBool)
  (HOLambda [LBool, LBool] LBool LBool
    (HOVar [LBool, LBool, LBool] LBool (LThere LHere)))

higherOrderArrowApplication : HigherOrderTerm [LBool] (LArrow LBool LBool)
  (CApplicationType (CLambdaType (CLambdaType (CVariable (LThere LHere)))) (CVariable LHere))
higherOrderArrowApplication = HOApplication [LBool] LBool (LArrow LBool LBool)
  Tests.Shadow.higherOrderArrowFunction Tests.Shadow.higherOrderUnitArgument

higherOrderArrowApplicationBeta :
  higherOrderTermSemantics Tests.Shadow.higherOrderArrowApplication =
    commonApply (higherOrderTermSemantics Tests.Shadow.higherOrderArrowFunction)
      (higherOrderTermSemantics Tests.Shadow.higherOrderUnitArgument)
higherOrderArrowApplicationBeta = higherOrderApplicationBeta
  Tests.Shadow.higherOrderArrowFunction Tests.Shadow.higherOrderUnitArgument

higherOrderArrowApplicationResult :
  applyMorphism (applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderArrowApplication) (True, ())) False = True
higherOrderArrowApplicationResult = trans
  (cong (\m => applyMorphism (applyMorphism m (True, ())) False)
    Tests.Shadow.higherOrderArrowApplicationBeta) Refl

higherOrderArrowApplicationPointwiseResult :
  applyMorphism (applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderArrowApplication) (False, ())) True = False
higherOrderArrowApplicationPointwiseResult = trans
  (cong (\m => applyMorphism m True)
    (higherOrderApplicationBetaAt Tests.Shadow.higherOrderArrowFunction
      Tests.Shadow.higherOrderUnitArgument (False, ()))) Refl

-- Exercise the alignment proof itself, not just the corresponding beta laws.
higherOrderAlignedUnitLeafResult :
  applyMorphism (higherOrderTermSemantics (HOUnit [LBool])) (True, ()) = ()
higherOrderAlignedUnitLeafResult = trans
  (higherOrderAlignedRelated (AlignUnit [LBool]) (True, ()) (True, ()) (Refl, Refl)) Refl

higherOrderAlignedFalseIfResult :
  applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderLinearIf) (False, ()) = False
higherOrderAlignedFalseIfResult = trans
  (higherOrderAlignedRelated Tests.Shadow.higherOrderLinearAlignment
    (False, ()) (False, ()) (Refl, Refl))
  Tests.Shadow.higherOrderLinearFalse

higherOrderUnitApplicationAlignment :
  HigherOrderAlignment Tests.Shadow.higherOrderUnitApplication Tests.Shadow.higherOrderUnitApplication
higherOrderUnitApplicationAlignment = AlignApplication
  (AlignLambda (AlignUnit [LBool, LBool])) (AlignVar [LBool] LBool LHere)

higherOrderAlignedUnitApplicationResult :
  applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderUnitApplication) (True, ()) = ()
higherOrderAlignedUnitApplicationResult = trans
  (higherOrderAlignedRelated Tests.Shadow.higherOrderUnitApplicationAlignment
    (True, ()) (True, ()) (Refl, Refl))
  Tests.Shadow.higherOrderUnitApplicationResult

higherOrderArrowApplicationAlignment :
  HigherOrderAlignment Tests.Shadow.higherOrderArrowApplication Tests.Shadow.higherOrderArrowApplication
higherOrderArrowApplicationAlignment = AlignApplication
  (AlignLambda (AlignLambda (AlignVar [LBool, LBool, LBool] LBool (LThere LHere))))
  (AlignVar [LBool] LBool LHere)

higherOrderAlignedArrowApplicationResult :
  applyMorphism (applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderArrowApplication) (True, ())) False = True
higherOrderAlignedArrowApplicationResult = trans
  (higherOrderAlignedRelated Tests.Shadow.higherOrderArrowApplicationAlignment
    (True, ()) (True, ()) (Refl, Refl) False False Refl)
  Tests.Shadow.higherOrderArrowApplicationResult

higherOrderDistinctApplicationRelated :
  related (commonTypeSetoid LBool)
    (applyMorphism (higherOrderTermSemantics (HOApplication [LBool, LArrow LBool LBool] LBool LBool
      (HOVar [LBool, LArrow LBool LBool] (LArrow LBool LBool) (LThere LHere))
      (HOVar [LBool, LArrow LBool LBool] LBool LHere))) (True, (Tests.Shadow.setoidIdentity, ())))
    (applyMorphism (higherOrderTermSemantics (HOApplication [LBool, LArrow LBool LBool] LBool LBool
      (HOVar [LBool, LArrow LBool LBool] (LArrow LBool LBool) (LThere LHere))
      (HOVar [LBool, LArrow LBool LBool] LBool LHere))) (True, (Tests.Shadow.setoidConditionalIdentity, ())))
higherOrderDistinctApplicationRelated =
  trans (cong (\m => applyMorphism m (True, (Tests.Shadow.setoidIdentity, ()))) beta)
    (trans (Tests.Shadow.setoidIdentityEquivalent True True Refl)
      (sym (cong (\m => applyMorphism m (True, (Tests.Shadow.setoidConditionalIdentity, ()))) beta)))
  where
    beta = higherOrderApplicationBeta
      (HOVar [LBool, LArrow LBool LBool] (LArrow LBool LBool) (LThere LHere))
      (HOVar [LBool, LArrow LBool LBool] LBool LHere)

higherOrderUnitElim : HigherOrderTerm [] LBool (CUnitEliminationType CUnitType (CBoolType {b = True}))
higherOrderUnitElim = HOUnitElim [] LBool (HOUnit []) (HOBool [] True)

higherOrderUnitElimResult : applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderUnitElim) () = True
higherOrderUnitElimResult = Refl

pathFirstComponent : CommonMorphism Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid
pathFirstComponent = MkCommonMorphism fst (\Refl => Refl)

pathVariable : HigherOrderPathTerm [] [LBool] LBool 1 (CPAtType {i = Var FZ} LHere)
pathVariable = HOPAt [] [LBool] LBool 1 LHere (Var FZ)

pathNonBoolean : applyMorphism (higherOrderPathSemantics Tests.Shadow.pathVariable (\_ => (True, False)))
  ((), (Tests.Shadow.pathFirstComponent, ())) = True
pathNonBoolean = Refl

higherPathEndpoint : applyMorphism (higherOrderPathSemantics Tests.Shadow.pathVariable (\_ => (False, False)))
  ((), (Tests.Shadow.pathFirstComponent, ())) = False
higherPathEndpoint = Refl

pathLinearIf : HigherOrderPathTerm [LBool] [LBool] LBool 1 (CPOrdinaryType (sourceCommonTyped Tests.Shadow.linearSource))
pathLinearIf = HOPOrdinary [LBool] [LBool] LBool 1 Tests.Shadow.higherOrderLinearIf

pathLinearIfResult : applyMorphism (higherOrderPathSemantics Tests.Shadow.pathLinearIf (\_ => (True, False)))
  ((True, ()), (Tests.Shadow.pathFirstComponent, ())) = True
pathLinearIfResult = Refl

pathCaptured : HigherOrderPathTerm [LBool] [LBool] LBool 1
  (CPAppType (CPLamType (CPIfType (CPAtType {i = Var FZ} LHere)
    (CPOrdinaryType (CVariable (LThere LHere))) (CPOrdinaryType (CBoolType {b = False}))))
    (CPOrdinaryType CUnitType))
pathCaptured = HOPApplication [LBool] [LBool] LUnit LBool 1
  (HOPLambda [LBool] [LBool] LUnit LBool 1
    (HOPIf [LUnit, LBool] [LBool] LBool 1
      (HOPAt [LUnit, LBool] [LBool] LBool 1 LHere (Var FZ))
      (HOPOrdinary [LUnit, LBool] [LBool] LBool 1 (HOVar [LUnit, LBool] LBool (LThere LHere)))
      (HOPOrdinary [LUnit, LBool] [LBool] LBool 1 (HOBool [LUnit, LBool] False))))
  (HOPOrdinary [LBool] [LBool] LUnit 1 (HOUnit [LBool]))

pathCapturedResult : applyMorphism (higherOrderPathSemantics Tests.Shadow.pathCaptured (\_ => (True, False)))
  ((True, ()), (Tests.Shadow.pathFirstComponent, ())) = True
pathCapturedResult = Refl

pathArrowOne : CommonMorphism Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid (commonTypeSetoid (LArrow LBool LBool))
pathArrowOne = commonConstant Tests.Shadow.setoidIdentity

pathArrowTwo : CommonMorphism Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid (commonTypeSetoid (LArrow LBool LBool))
pathArrowTwo = commonConstant Tests.Shadow.setoidConditionalIdentity

pathArrowRelated : morphismsRelated Tests.Shadow.pathArrowOne Tests.Shadow.pathArrowTwo
pathArrowRelated x x Refl = Tests.Shadow.setoidIdentityEquivalent

pathArrowWitness : HigherOrderPathTerm [] [LArrow LBool LBool] (LArrow LBool LBool) 1
  (CPLamType (CPAppType (CPAtType {i = Var FZ} LHere) (CPOrdinaryType (CVariable LHere))))
pathArrowWitness = HOPLambda [] [LArrow LBool LBool] LBool LBool 1
  (HOPApplication [LBool] [LArrow LBool LBool] LBool LBool 1
    (HOPAt [LBool] [LArrow LBool LBool] (LArrow LBool LBool) 1 LHere (Var FZ))
    (HOPOrdinary [LBool] [LArrow LBool LBool] LBool 1 (HOVar [LBool] LBool LHere)))

pathArrowSemanticRelated : related (commonTypeSetoid (LArrow LBool LBool))
  (applyMorphism (higherOrderPathSemantics Tests.Shadow.pathArrowWitness (\_ => (True, False))) ((), (Tests.Shadow.pathArrowOne, ())))
  (applyMorphism (higherOrderPathSemantics Tests.Shadow.pathArrowWitness (\_ => (True, False))) ((), (Tests.Shadow.pathArrowTwo, ())))
pathArrowSemanticRelated = respectsRelation (higherOrderPathSemantics Tests.Shadow.pathArrowWitness (\_ => (True, False)))
  {x = ((), (Tests.Shadow.pathArrowOne, ()))} {y = ((), (Tests.Shadow.pathArrowTwo, ()))}
  (Refl, (Tests.Shadow.pathArrowRelated, Refl))

pathUnitElimination : HigherOrderPathTerm [] [LBool] LBool 1
  (CPUnitElimType (CPOrdinaryType CUnitType) (CPAtType {i = Var FZ} LHere))
pathUnitElimination = HOPUnitElim [] [LBool] LBool 1
  (HOPOrdinary [] [LBool] LUnit 1 (HOUnit []))
  (HOPAt [] [LBool] LBool 1 LHere (Var FZ))

pathUnitEliminationResult : applyMorphism (higherOrderPathSemantics Tests.Shadow.pathUnitElimination (\_ => (True, False)))
  ((), (Tests.Shadow.pathFirstComponent, ())) = True
pathUnitEliminationResult = Refl

higherOrderConstantDeclarations : CommonDeclarations [] [LBool]
higherOrderConstantDeclarations = CommonDeclarePath (CBool False) (CBool True) CBoolType CBoolType CommonNoPaths

higherOrderConstantPaths : carrier (commonPathEnvironmentSetoid [LBool])
higherOrderConstantPaths = (Tests.Shadow.pathFirstComponent, ())

higherOrderConstantAdmissible : HigherOrderAdmissible Tests.Shadow.higherOrderConstantDeclarations Tests.Shadow.higherOrderConstantPaths
higherOrderConstantAdmissible = HOAdmissibleCons (HOBool [] False) (HOBool [] True)
  (\env => Refl) (\env => Refl) HOAdmissibleNil

higherOrderConstantLeft : applyMorphism Tests.Shadow.pathFirstComponent (False, False) = False
higherOrderConstantLeft = case higherOrderDeclaredLeftAtFace CommonDeclaredHere
  Tests.Shadow.higherOrderConstantPaths Tests.Shadow.higherOrderConstantAdmissible ()
  (\_ => (False, False)) (the (ScopedFace 1) (SEndpoint FZ False)) (Var FZ) Refl Refl of
    HOEndpointAtFace (HOBool _ False) prf => prf

higherOrderIfDeclarations : CommonDeclarations [] [LBool]
higherOrderIfDeclarations = CommonDeclarePath (CIf (CBool True) (CBool False) (CBool True)) (CBool True)
  (CConditionalType CBoolType CBoolType CBoolType) CBoolType CommonNoPaths

higherOrderIfAdmissible : HigherOrderAdmissible Tests.Shadow.higherOrderIfDeclarations Tests.Shadow.higherOrderConstantPaths
higherOrderIfAdmissible = HOAdmissibleCons
  (HOIf [] LBool (HOBool [] True) (HOBool [] False) (HOBool [] True)) (HOBool [] True)
  (\env => Refl) (\env => Refl) HOAdmissibleNil

higherOrderConstantRight : applyMorphism Tests.Shadow.pathFirstComponent (True, True) = True
higherOrderConstantRight = case higherOrderDeclaredRightAtFace CommonDeclaredHere
  Tests.Shadow.higherOrderConstantPaths Tests.Shadow.higherOrderIfAdmissible ()
  (\_ => (True, True)) (the (ScopedFace 1) (SEndpoint FZ True)) (Var FZ) Refl Refl of
    HOEndpointAtFace (HOBool _ True) prf => prf

-- The head is constantly True; the distinct tail has False and True endpoints.
higherOrderTailTestHead : CommonMorphism Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid
higherOrderTailTestHead = commonConstant True

higherOrderTailTestDeclarations : CommonDeclarations [] [LBool, LBool]
higherOrderTailTestDeclarations = CommonDeclarePath (CBool True) (CBool True) CBoolType CBoolType
  Tests.Shadow.higherOrderConstantDeclarations

higherOrderTailTestPaths : carrier (commonPathEnvironmentSetoid [LBool, LBool])
higherOrderTailTestPaths = (Tests.Shadow.higherOrderTailTestHead, Tests.Shadow.higherOrderConstantPaths)

higherOrderTailTestAdmissible : HigherOrderAdmissible Tests.Shadow.higherOrderTailTestDeclarations Tests.Shadow.higherOrderTailTestPaths
higherOrderTailTestAdmissible = HOAdmissibleCons (HOBool [] True) (HOBool [] True)
  (\env => Refl) (\env => Refl) Tests.Shadow.higherOrderConstantAdmissible

higherOrderTailLookupEndpoints :
  (applyMorphism Tests.Shadow.pathFirstComponent (False, False) = False,
   applyMorphism Tests.Shadow.pathFirstComponent (True, True) = True)
higherOrderTailLookupEndpoints = case higherOrderDeclaredLookup (CommonDeclaredThere CommonDeclaredHere)
  Tests.Shadow.higherOrderTailTestPaths Tests.Shadow.higherOrderTailTestAdmissible of
    HOEndpoints (HOBool _ False) (HOBool _ True) zero one => (zero (), one ())

-- No independent fixed path can have the ordinary Bool variable as its zero
-- endpoint for every ordinary environment.
higherOrderVariableEndpointDeclarations : CommonDeclarations [LBool] [LBool]
higherOrderVariableEndpointDeclarations = CommonDeclarePath (CVar FZ) (CBool True)
  (CVariable LHere) CBoolType CommonNoPaths

higherOrderVariableEndpointNotAdmissible :
  (path : CommonMorphism Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid) ->
  HigherOrderAdmissible Tests.Shadow.higherOrderVariableEndpointDeclarations (path, ()) -> Void
higherOrderVariableEndpointNotAdmissible path adm =
  case higherOrderDeclaredLookup CommonDeclaredHere (path, ()) adm of
    HOEndpoints (HOVar _ _ LHere) right zero one =>
      falseNotTrue (trans (sym (zero (False, ()))) (zero (True, ())))
  where
    falseNotTrue : False = True -> Void
    falseNotTrue Refl impossible

-- The two non-Boolean interval values flip the captured Boolean; endpoints do not.
dependentFlip : Bool -> DM -> Bool
dependentFlip b (False, False) = b
dependentFlip b (True, True) = b
dependentFlip b (False, True) = not b
dependentFlip b (True, False) = not b

dependentLinearPath : CommonMorphism
  (commonProductSetoid (commonEnvironmentSetoid [LBool]) Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid)
  Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid
dependentLinearPath = MkCommonMorphism (\input => dependentFlip (fst (fst input)) (snd input))
  (\{x}, {y}, rel => cong2 dependentFlip (fst (fst rel)) (snd rel))

dependentLinearPaths : carrier (commonDependentPathEnvironmentSetoid [LBool] [LBool])
dependentLinearPaths = (Tests.Shadow.dependentLinearPath, ())

dependentLinearDeclarations : CommonDeclarations [LBool] [LBool]
dependentLinearDeclarations = commonDeclarations
  (DeclarePath (shadowTerm Tests.Shadow.linearSource) (shadowTerm Tests.Shadow.linearSource) NoPaths)

dependentLinearEndpoint : (b : Bool) -> dependentFlip b (False, False) =
  applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderLinearIf) (b, ())
dependentLinearEndpoint False = Refl
dependentLinearEndpoint True = Refl

dependentLinearAdmissible : DependentPathAdmissible Tests.Shadow.dependentLinearDeclarations Tests.Shadow.dependentLinearPaths
dependentLinearAdmissible = DependentAdmissibleCons Tests.Shadow.higherOrderLinearIf Tests.Shadow.higherOrderLinearIf
  (\(b, ()) => Tests.Shadow.dependentLinearEndpoint b)
  (\(b, ()) => Tests.Shadow.dependentLinearEndpoint b) DependentAdmissibleNil

dependentLinearAt : HigherOrderPathTerm [LBool] [LBool] LBool 1 (CPAtType {i = Var FZ} LHere)
dependentLinearAt = HOPAt [LBool] [LBool] LBool 1 LHere (Var FZ)

dependentNonBooleanFalse : applyMorphism (dependentPathSemantics Tests.Shadow.dependentLinearAt (\_ => (True, False)))
  ((False, ()), Tests.Shadow.dependentLinearPaths) = True
dependentNonBooleanFalse = Refl

dependentNonBooleanTrue : applyMorphism (dependentPathSemantics Tests.Shadow.dependentLinearAt (\_ => (False, True)))
  ((True, ()), Tests.Shadow.dependentLinearPaths) = False
dependentNonBooleanTrue = Refl

dependentBinder : HigherOrderPathTerm [LBool] [LBool] (LArrow LBool LBool) 1
  (CPLamType (CPAtType {i = Var FZ} LHere))
dependentBinder = HOPLambda [LBool] [LBool] LBool LBool 1
  (HOPAt [LBool, LBool] [LBool] LBool 1 LHere (Var FZ))

dependentBinderNoCapture : applyMorphism (applyMorphism (dependentPathSemantics Tests.Shadow.dependentBinder (\_ => (True, False)))
  ((False, ()), Tests.Shadow.dependentLinearPaths)) True = True
dependentBinderNoCapture = Refl

dependentLinearFace : (b : Bool) -> DependentEndpointAtFace [LBool] {paths = [LBool]} LHere
  (commonTerm (shadowTerm Tests.Shadow.linearSource)) Tests.Shadow.dependentLinearPaths (b, ()) (False, False)
dependentLinearFace b = dependentDeclaredLeftAtFace CommonDeclaredHere Tests.Shadow.dependentLinearPaths
  Tests.Shadow.dependentLinearAdmissible (b, ()) (\_ => (False, False))
  (the (ScopedFace 1) (SEndpoint FZ False)) (Var FZ) Refl Refl

dependentBinderOtherArgument : applyMorphism (applyMorphism (dependentPathSemantics Tests.Shadow.dependentBinder (\_ => (True, False)))
  ((False, ()), Tests.Shadow.dependentLinearPaths)) False = True
dependentBinderOtherArgument = Refl

dependentBinderOtherEnvironment : applyMorphism (applyMorphism (dependentPathSemantics Tests.Shadow.dependentBinder (\_ => (True, False)))
  ((True, ()), Tests.Shadow.dependentLinearPaths)) True = False
dependentBinderOtherEnvironment = Refl

-- The second declaration has genuinely different left and right syntax.
dependentTailPath : CommonMorphism
  (commonProductSetoid (commonEnvironmentSetoid []) Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid)
  Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid
dependentTailPath = MkCommonMorphism (\input => fst (snd input))
  (\rel => cong fst (snd rel))

dependentTwoDeclarations : CommonDeclarations [] [LBool, LBool]
dependentTwoDeclarations = CommonDeclarePath (CBool True) (CBool True) CBoolType CBoolType
  (CommonDeclarePath (CBool False) (CBool True) CBoolType CBoolType CommonNoPaths)

dependentTwoPaths : carrier (commonDependentPathEnvironmentSetoid [] [LBool, LBool])
dependentTwoPaths = (commonConstant True, (Tests.Shadow.dependentTailPath, ()))

dependentTwoAdmissible : DependentPathAdmissible Tests.Shadow.dependentTwoDeclarations Tests.Shadow.dependentTwoPaths
dependentTwoAdmissible = DependentAdmissibleCons (HOBool [] True) (HOBool [] True)
  (\_ => Refl) (\_ => Refl)
  (DependentAdmissibleCons (HOBool [] False) (HOBool [] True)
    (\_ => Refl) (\_ => Refl) DependentAdmissibleNil)

dependentTailLeftFace : applyMorphism Tests.Shadow.dependentTailPath ((), (False, False)) = False
dependentTailLeftFace = case dependentDeclaredLeftAtFace (CommonDeclaredThere CommonDeclaredHere)
  Tests.Shadow.dependentTwoPaths Tests.Shadow.dependentTwoAdmissible () (\_ => (False, False))
  (the (ScopedFace 1) (SEndpoint FZ False)) (Var FZ) Refl Refl of
    DependentAtFace (HOBool _ False) rel => rel

dependentTailRightFace : applyMorphism Tests.Shadow.dependentTailPath ((), (True, True)) = True
dependentTailRightFace = case dependentDeclaredRightAtFace (CommonDeclaredThere CommonDeclaredHere)
  Tests.Shadow.dependentTwoPaths Tests.Shadow.dependentTwoAdmissible () (\_ => (True, True))
  (the (ScopedFace 1) (SEndpoint FZ True)) (Var FZ) Refl Refl of
    DependentAtFace (HOBool _ True) rel => rel

-- A syntactically different path morphism, related extensionally to the first.
dependentDoubleNot : (b : Bool) -> b = not (not b)
dependentDoubleNot False = Refl
dependentDoubleNot True = Refl

dependentLinearPathAlternative : CommonMorphism
  (commonProductSetoid (commonEnvironmentSetoid [LBool]) Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid)
  Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid
dependentLinearPathAlternative = MkCommonMorphism
  (\input => not (not (dependentFlip (fst (fst input)) (snd input))))
  (\rel => cong (\b => not (not b)) (cong2 dependentFlip (fst (fst rel)) (snd rel)))

dependentLinearPathsRelated : related (commonDependentPathEnvironmentSetoid [LBool] [LBool])
  Tests.Shadow.dependentLinearPaths (Tests.Shadow.dependentLinearPathAlternative, ())
dependentLinearPathsRelated =
  (\x, y, xy => trans (respectsRelation Tests.Shadow.dependentLinearPath {x} {y} xy)
    (Tests.Shadow.dependentDoubleNot (applyMorphism Tests.Shadow.dependentLinearPath y)), Refl)

-- This relation goes through the lambda interpreter and its path weakening.
dependentBinderExtensional : related (commonTypeSetoid (LArrow LBool LBool))
  (applyMorphism (dependentPathSemantics Tests.Shadow.dependentBinder (\_ => (True, False)))
    ((False, ()), Tests.Shadow.dependentLinearPaths))
  (applyMorphism (dependentPathSemantics Tests.Shadow.dependentBinder (\_ => (True, False)))
    ((False, ()), (Tests.Shadow.dependentLinearPathAlternative, ())))
dependentBinderExtensional = respectsRelation (dependentPathSemantics Tests.Shadow.dependentBinder (\_ => (True, False)))
  {x = ((False, ()), Tests.Shadow.dependentLinearPaths)}
  {y = ((False, ()), (Tests.Shadow.dependentLinearPathAlternative, ()))}
  ((Refl, Refl), Tests.Shadow.dependentLinearPathsRelated)

dependentBinderExtensionalApplied :
  applyMorphism (applyMorphism (dependentPathSemantics Tests.Shadow.dependentBinder (\_ => (True, False)))
    ((False, ()), Tests.Shadow.dependentLinearPaths)) True =
  applyMorphism (applyMorphism (dependentPathSemantics Tests.Shadow.dependentBinder (\_ => (True, False)))
    ((False, ()), (Tests.Shadow.dependentLinearPathAlternative, ()))) True
dependentBinderExtensionalApplied = Tests.Shadow.dependentBinderExtensional True True Refl

-- Identical unannotated syntax can use distinct application argument types.
ambiguousBoolArrow : HigherOrderTerm [] LBool
  (CApplicationType {a = LArrow LBool LBool} (CLambdaType (CBoolType {b = True})) (CLambdaType (CVariable LHere)))
ambiguousBoolArrow = HOApplication [] (LArrow LBool LBool) LBool
  (HOLambda [] (LArrow LBool LBool) LBool (HOBool [LArrow LBool LBool] True))
  (HOLambda [] LBool LBool (HOVar [LBool] LBool LHere))

ambiguousUnitArrow : HigherOrderTerm [] LBool
  (CApplicationType {a = LArrow LUnit LUnit} (CLambdaType (CBoolType {b = True})) (CLambdaType (CVariable LHere)))
ambiguousUnitArrow = HOApplication [] (LArrow LUnit LUnit) LBool
  (HOLambda [] (LArrow LUnit LUnit) LBool (HOBool [LArrow LUnit LUnit] True))
  (HOLambda [] LUnit LUnit (HOVar [LUnit] LUnit LHere))

ambiguousArrowDomainsDiffer : LArrow LBool LBool = LArrow LUnit LUnit -> Void
ambiguousArrowDomainsDiffer Refl impossible

dependentSameWitnessBinder : related (commonTypeSetoid (LArrow LBool LBool))
  (applyMorphism (dependentPathSemantics Tests.Shadow.dependentBinder (\_ => (True, False)))
    ((False, ()), Tests.Shadow.dependentLinearPaths))
  (applyMorphism (dependentPathSemantics Tests.Shadow.dependentBinder (\_ => (True, False)))
    ((False, ()), (Tests.Shadow.dependentLinearPathAlternative, ())))
dependentSameWitnessBinder = dependentPathSameWitness Tests.Shadow.dependentBinder (\_ => (True, False))
  ((False, ()), Tests.Shadow.dependentLinearPaths)
  ((False, ()), (Tests.Shadow.dependentLinearPathAlternative, ()))
  ((Refl, Refl), Tests.Shadow.dependentLinearPathsRelated)

dependentSameWitnessLinearIf : related (commonTypeSetoid LBool)
  (applyMorphism (dependentPathSemantics Tests.Shadow.pathLinearIf (\_ => (True, False)))
    ((True, ()), Tests.Shadow.dependentLinearPaths))
  (applyMorphism (dependentPathSemantics Tests.Shadow.pathLinearIf (\_ => (True, False)))
    ((True, ()), (Tests.Shadow.dependentLinearPathAlternative, ())))
dependentSameWitnessLinearIf = dependentPathSameWitness Tests.Shadow.pathLinearIf (\_ => (True, False))
  ((True, ()), Tests.Shadow.dependentLinearPaths)
  ((True, ()), (Tests.Shadow.dependentLinearPathAlternative, ()))
  ((Refl, Refl), Tests.Shadow.dependentLinearPathsRelated)

dependentSameWitnessApplication : related (commonTypeSetoid LBool)
  (applyMorphism (dependentPathSemantics Tests.Shadow.pathCaptured (\_ => (True, False)))
    ((True, ()), Tests.Shadow.dependentLinearPaths))
  (applyMorphism (dependentPathSemantics Tests.Shadow.pathCaptured (\_ => (True, False)))
    ((True, ()), (Tests.Shadow.dependentLinearPathAlternative, ())))
dependentSameWitnessApplication = dependentPathSameWitness Tests.Shadow.pathCaptured (\_ => (True, False))
  ((True, ()), Tests.Shadow.dependentLinearPaths)
  ((True, ()), (Tests.Shadow.dependentLinearPathAlternative, ()))
  ((Refl, Refl), Tests.Shadow.dependentLinearPathsRelated)

alignmentApplicationRelatedTest :
  related (commonTypeSetoid LBool)
    (applyMorphism Tests.Shadow.setoidIdentity True)
    (applyMorphism Tests.Shadow.setoidConditionalIdentity True)
alignmentApplicationRelatedTest = higherOrderApplicationRelated {arg = LBool} {result = LBool}
  {f = Tests.Shadow.setoidIdentity} {g = Tests.Shadow.setoidConditionalIdentity}
  {x = True} {y = True} Tests.Shadow.setoidIdentityEquivalent Refl

alignmentApplicationRelatedArrowInputs :
  related (commonTypeSetoid (LArrow LBool LBool))
    (applyMorphism Tests.Shadow.higherIdentity Tests.Shadow.setoidIdentity)
    (applyMorphism Tests.Shadow.higherIdentity Tests.Shadow.setoidConditionalIdentity)
alignmentApplicationRelatedArrowInputs = higherOrderApplicationRelated
  {arg = LArrow LBool LBool} {result = LArrow LBool LBool}
  {f = Tests.Shadow.higherIdentity} {g = Tests.Shadow.higherIdentity}
  {x = Tests.Shadow.setoidIdentity} {y = Tests.Shadow.setoidConditionalIdentity}
  (\left, right, rel => rel) Tests.Shadow.setoidIdentityEquivalent

alignmentChoiceRelatedFalse :
  related (commonTypeSetoid LBool)
    (commonChoose False True False) (commonChoose False True False)
alignmentChoiceRelatedFalse = higherOrderChoiceRelated {a = LBool} False False Refl
  {lt = True} {rt = True} {lf = False} {rf = False} Refl Refl

alignmentChoiceRelatedTest :
  related (commonTypeSetoid (LArrow LBool LBool))
    (commonChoose True Tests.Shadow.setoidIdentity Tests.Shadow.setoidIdentity)
    (commonChoose True Tests.Shadow.setoidConditionalIdentity Tests.Shadow.setoidConditionalIdentity)
alignmentChoiceRelatedTest = higherOrderChoiceRelated {a = LArrow LBool LBool} True True Refl
  {lt = Tests.Shadow.setoidIdentity} {rt = Tests.Shadow.setoidConditionalIdentity}
  {lf = Tests.Shadow.setoidIdentity} {rf = Tests.Shadow.setoidConditionalIdentity}
  Tests.Shadow.setoidIdentityEquivalent Tests.Shadow.setoidIdentityEquivalent

alignmentVariableRelatedTest :
  related (commonTypeSetoid (LArrow LBool LBool))
    (applyMorphism (higherOrderTermSemantics (HOVar [LArrow LBool LBool] (LArrow LBool LBool) LHere))
      (Tests.Shadow.setoidIdentity, ()))
    (applyMorphism (higherOrderTermSemantics (HOVar [LArrow LBool LBool] (LArrow LBool LBool) LHere))
      (Tests.Shadow.setoidConditionalIdentity, ()))
alignmentVariableRelatedTest = higherOrderAlignedVariableRelated [LArrow LBool LBool] (LArrow LBool LBool) LHere
  (Tests.Shadow.setoidIdentity, ()) (Tests.Shadow.setoidConditionalIdentity, ())
  (Tests.Shadow.setoidIdentityEquivalent, Refl)

pathLinearAlignment : HigherOrderPathAlignment Tests.Shadow.pathLinearIf Tests.Shadow.pathLinearIf
pathLinearAlignment = AlignPathOrdinary Tests.Shadow.higherOrderLinearAlignment

pathCapturedAlignment : HigherOrderPathAlignment Tests.Shadow.pathCaptured Tests.Shadow.pathCaptured
pathCapturedAlignment = AlignPathApplication
  (AlignPathLambda (AlignPathIf (AlignPathAt [LUnit, LBool] [LBool] LBool 1 LHere (Var FZ))
    (AlignPathOrdinary (AlignVar [LUnit, LBool] LBool (LThere LHere)))
    (AlignPathOrdinary (AlignBool [LUnit, LBool] False))))
  (AlignPathOrdinary (AlignUnit [LBool]))

pathArrowAlignment : HigherOrderPathAlignment Tests.Shadow.pathArrowWitness Tests.Shadow.pathArrowWitness
pathArrowAlignment = AlignPathLambda (AlignPathApplication
  (AlignPathAt [LBool] [LArrow LBool LBool] (LArrow LBool LBool) 1 LHere (Var FZ))
  (AlignPathOrdinary (AlignVar [LBool] LBool LHere)))

pathUnitEliminationAlignment : HigherOrderPathAlignment Tests.Shadow.pathUnitElimination Tests.Shadow.pathUnitElimination
pathUnitEliminationAlignment = AlignPathUnitElim (AlignPathOrdinary (AlignUnit []))
  (AlignPathAt [] [LBool] LBool 1 LHere (Var FZ))

dependentCapturedAligned : related (commonTypeSetoid LBool)
  (applyMorphism (dependentPathSemantics Tests.Shadow.pathCaptured (\_ => (True, False))) ((False, ()), Tests.Shadow.dependentLinearPaths))
  (applyMorphism (dependentPathSemantics Tests.Shadow.pathCaptured (\_ => (True, False))) ((False, ()), Tests.Shadow.dependentLinearPaths))
dependentCapturedAligned = dependentPathAlignedRelated Tests.Shadow.pathCapturedAlignment (\_ => (True, False))
  ((False, ()), Tests.Shadow.dependentLinearPaths) ((False, ()), Tests.Shadow.dependentLinearPaths)
  ((Refl, Refl), ((\x, y, xy => respectsRelation Tests.Shadow.dependentLinearPath xy), Refl))

dependentArrowOne : CommonMorphism
  (commonProductSetoid (commonEnvironmentSetoid []) Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid)
  (commonTypeSetoid (LArrow LBool LBool))
dependentArrowOne = commonConstant Tests.Shadow.setoidIdentity

dependentArrowTwo : CommonMorphism
  (commonProductSetoid (commonEnvironmentSetoid []) Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid)
  (commonTypeSetoid (LArrow LBool LBool))
dependentArrowTwo = commonConstant Tests.Shadow.setoidConditionalIdentity

dependentArrowAligned : related (commonTypeSetoid (LArrow LBool LBool))
  (applyMorphism (dependentPathSemantics Tests.Shadow.pathArrowWitness (\_ => (True, False))) ((), (Tests.Shadow.dependentArrowOne, ())))
  (applyMorphism (dependentPathSemantics Tests.Shadow.pathArrowWitness (\_ => (True, False))) ((), (Tests.Shadow.dependentArrowTwo, ())))
dependentArrowAligned = dependentPathAlignedRelated Tests.Shadow.pathArrowAlignment (\_ => (True, False))
  ((), (Tests.Shadow.dependentArrowOne, ())) ((), (Tests.Shadow.dependentArrowTwo, ()))
  (Refl, ((\x, y, xy => Tests.Shadow.setoidIdentityEquivalent), Refl))

-- Related but definitionally different ordinary environments and dependent paths.
alignedEnvPath1 : CommonMorphism
  (commonProductSetoid (commonEnvironmentSetoid [LArrow LBool LBool]) Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid)
  Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid
alignedEnvPath1 = MkCommonMorphism (\input => fst (snd input)) (\rel => cong fst (snd rel))

alignedEnvPath2 : CommonMorphism
  (commonProductSetoid (commonEnvironmentSetoid [LArrow LBool LBool]) Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid)
  Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid
alignedEnvPath2 = MkCommonMorphism (\input => if fst (snd input) then True else False)
  (\rel => cong (\v => if fst v then True else False) (snd rel))

alignedEnvPathRelated : related (commonDependentPathEnvironmentSetoid [LArrow LBool LBool] [LBool])
  (Tests.Shadow.alignedEnvPath1, ()) (Tests.Shadow.alignedEnvPath2, ())
alignedEnvPathRelated = ((\x, y, xy => trans (cong fst (snd xy)) (boolIdentity (fst (snd y)))), Refl)
  where
    boolIdentity : (b : Bool) -> b = (if b then True else False)
    boolIdentity False = Refl
    boolIdentity True = Refl

alignedBoolApp : HigherOrderPathTerm [LArrow LBool LBool] [LBool] LBool 1
  (CPAppType (CPOrdinaryType (CVariable LHere)) (CPAtType {i = Var FZ} LHere))
alignedBoolApp = HOPApplication [LArrow LBool LBool] [LBool] LBool LBool 1
  (HOPOrdinary [LArrow LBool LBool] [LBool] (LArrow LBool LBool) 1 (HOVar [LArrow LBool LBool] (LArrow LBool LBool) LHere))
  (HOPAt [LArrow LBool LBool] [LBool] LBool 1 LHere (Var FZ))

alignedBoolAppWitness : HigherOrderPathAlignment Tests.Shadow.alignedBoolApp Tests.Shadow.alignedBoolApp
alignedBoolAppWitness = AlignPathApplication
  (AlignPathOrdinary (AlignVar [LArrow LBool LBool] (LArrow LBool LBool) LHere))
  (AlignPathAt [LArrow LBool LBool] [LBool] LBool 1 LHere (Var FZ))

alignedBoolAppRelated : applyMorphism (dependentPathSemantics Tests.Shadow.alignedBoolApp (\_ => (True, False)))
  ((Tests.Shadow.setoidIdentity, ()), (Tests.Shadow.alignedEnvPath1, ())) =
  applyMorphism (dependentPathSemantics Tests.Shadow.alignedBoolApp (\_ => (True, False)))
  ((Tests.Shadow.setoidConditionalIdentity, ()), (Tests.Shadow.alignedEnvPath2, ()))
alignedBoolAppRelated = dependentPathAlignedRelated Tests.Shadow.alignedBoolAppWitness (\_ => (True, False))
  ((Tests.Shadow.setoidIdentity, ()), (Tests.Shadow.alignedEnvPath1, ()))
  ((Tests.Shadow.setoidConditionalIdentity, ()), (Tests.Shadow.alignedEnvPath2, ()))
  ((Tests.Shadow.setoidIdentityEquivalent, Refl), Tests.Shadow.alignedEnvPathRelated)

alignedBoolAppResult : applyMorphism (dependentPathSemantics Tests.Shadow.alignedBoolApp (\_ => (True, False)))
  ((Tests.Shadow.setoidIdentity, ()), (Tests.Shadow.alignedEnvPath1, ())) = True
alignedBoolAppResult = trans Tests.Shadow.alignedBoolAppRelated Refl

alignedUnitApp : HigherOrderPathTerm [LArrow LBool LBool] [LBool] LUnit 1
  (CPAppType (CPLamType (CPOrdinaryType CUnitType)) (CPAtType {i = Var FZ} LHere))
alignedUnitApp = HOPApplication [LArrow LBool LBool] [LBool] LBool LUnit 1
  (HOPLambda [LArrow LBool LBool] [LBool] LBool LUnit 1
    (HOPOrdinary [LBool, LArrow LBool LBool] [LBool] LUnit 1 (HOUnit [LBool, LArrow LBool LBool])))
  (HOPAt [LArrow LBool LBool] [LBool] LBool 1 LHere (Var FZ))

alignedUnitAppWitness : HigherOrderPathAlignment Tests.Shadow.alignedUnitApp Tests.Shadow.alignedUnitApp
alignedUnitAppWitness = AlignPathApplication (AlignPathLambda (AlignPathOrdinary (AlignUnit [LBool, LArrow LBool LBool])))
  (AlignPathAt [LArrow LBool LBool] [LBool] LBool 1 LHere (Var FZ))

alignedUnitAppResult : applyMorphism (dependentPathSemantics Tests.Shadow.alignedUnitApp (\_ => (True, False)))
  ((Tests.Shadow.setoidIdentity, ()), (Tests.Shadow.alignedEnvPath1, ())) = ()
alignedUnitAppResult = trans (dependentPathAlignedRelated Tests.Shadow.alignedUnitAppWitness (\_ => (True, False))
  ((Tests.Shadow.setoidIdentity, ()), (Tests.Shadow.alignedEnvPath1, ()))
  ((Tests.Shadow.setoidConditionalIdentity, ()), (Tests.Shadow.alignedEnvPath2, ()))
  ((Tests.Shadow.setoidIdentityEquivalent, Refl), Tests.Shadow.alignedEnvPathRelated)) Refl

alignedArrowApp : HigherOrderPathTerm [LArrow LBool LBool] [LBool] (LArrow LBool LBool) 1
  (CPAppType (CPLamType (CPOrdinaryType (CVariable (LThere LHere)))) (CPAtType {i = Var FZ} LHere))
alignedArrowApp = HOPApplication [LArrow LBool LBool] [LBool] LBool (LArrow LBool LBool) 1
  (HOPLambda [LArrow LBool LBool] [LBool] LBool (LArrow LBool LBool) 1
    (HOPOrdinary [LBool, LArrow LBool LBool] [LBool] (LArrow LBool LBool) 1
      (HOVar [LBool, LArrow LBool LBool] (LArrow LBool LBool) (LThere LHere))))
  (HOPAt [LArrow LBool LBool] [LBool] LBool 1 LHere (Var FZ))

alignedArrowAppWitness : HigherOrderPathAlignment Tests.Shadow.alignedArrowApp Tests.Shadow.alignedArrowApp
alignedArrowAppWitness = AlignPathApplication
  (AlignPathLambda (AlignPathOrdinary (AlignVar [LBool, LArrow LBool LBool] (LArrow LBool LBool) (LThere LHere))))
  (AlignPathAt [LArrow LBool LBool] [LBool] LBool 1 LHere (Var FZ))

alignedArrowAppResult : applyMorphism (applyMorphism (dependentPathSemantics Tests.Shadow.alignedArrowApp (\_ => (True, False)))
  ((Tests.Shadow.setoidIdentity, ()), (Tests.Shadow.alignedEnvPath1, ()))) True = True
alignedArrowAppResult = trans ((dependentPathAlignedRelated Tests.Shadow.alignedArrowAppWitness (\_ => (True, False))
  ((Tests.Shadow.setoidIdentity, ()), (Tests.Shadow.alignedEnvPath1, ()))
  ((Tests.Shadow.setoidConditionalIdentity, ()), (Tests.Shadow.alignedEnvPath2, ()))
  ((Tests.Shadow.setoidIdentityEquivalent, Refl), Tests.Shadow.alignedEnvPathRelated)) True True Refl) Refl

-- The captured path selects opposite branches at the same non-Boolean valuation.
capturedTrueBranchRelated : applyMorphism (dependentPathSemantics Tests.Shadow.pathCaptured (\_ => (True, False)))
  ((False, ()), Tests.Shadow.dependentLinearPaths) =
  applyMorphism (dependentPathSemantics Tests.Shadow.pathCaptured (\_ => (True, False)))
  ((False, ()), (Tests.Shadow.dependentLinearPathAlternative, ()))
capturedTrueBranchRelated = dependentPathAlignedRelated Tests.Shadow.pathCapturedAlignment (\_ => (True, False))
  ((False, ()), Tests.Shadow.dependentLinearPaths) ((False, ()), (Tests.Shadow.dependentLinearPathAlternative, ()))
  ((Refl, Refl), Tests.Shadow.dependentLinearPathsRelated)

capturedTrueBranchResult : applyMorphism (dependentPathSemantics Tests.Shadow.pathCaptured (\_ => (True, False)))
  ((False, ()), Tests.Shadow.dependentLinearPaths) = False
capturedTrueBranchResult = trans Tests.Shadow.capturedTrueBranchRelated Refl

capturedFalseBranchResult : applyMorphism (dependentPathSemantics Tests.Shadow.pathCaptured (\_ => (True, False)))
  ((True, ()), Tests.Shadow.dependentLinearPaths) = False
capturedFalseBranchResult = trans (dependentPathAlignedRelated Tests.Shadow.pathCapturedAlignment (\_ => (True, False))
  ((True, ()), Tests.Shadow.dependentLinearPaths) ((True, ()), (Tests.Shadow.dependentLinearPathAlternative, ()))
  ((Refl, Refl), Tests.Shadow.dependentLinearPathsRelated)) Refl

linearPathAlignedResult : applyMorphism (dependentPathSemantics Tests.Shadow.pathLinearIf (\_ => (True, False)))
  ((True, ()), Tests.Shadow.dependentLinearPaths) = True
linearPathAlignedResult = trans (dependentPathAlignedRelated Tests.Shadow.pathLinearAlignment (\_ => (True, False))
  ((True, ()), Tests.Shadow.dependentLinearPaths) ((True, ()), (Tests.Shadow.dependentLinearPathAlternative, ()))
  ((Refl, Refl), Tests.Shadow.dependentLinearPathsRelated)) Refl

unitElimAlignedResult : applyMorphism (dependentPathSemantics Tests.Shadow.pathUnitElimination (\_ => (True, False)))
  ((), (Tests.Shadow.dependentTailPath, ())) = True
unitElimAlignedResult = trans (dependentPathAlignedRelated Tests.Shadow.pathUnitEliminationAlignment (\_ => (True, False))
  ((), (Tests.Shadow.dependentTailPath, ())) ((), (Tests.Shadow.dependentTailPath, ()))
  (Refl, ((\x, y, xy => respectsRelation Tests.Shadow.dependentTailPath xy), Refl))) Refl

alignedIf : HigherOrderPathTerm [LArrow LBool LBool] [LBool] LBool 1
  (CPIfType (CPAtType {i = Var FZ} LHere) (CPOrdinaryType (CBoolType {b = True})) (CPOrdinaryType (CBoolType {b = False})))
alignedIf = HOPIf [LArrow LBool LBool] [LBool] LBool 1
  (HOPAt [LArrow LBool LBool] [LBool] LBool 1 LHere (Var FZ))
  (HOPOrdinary [LArrow LBool LBool] [LBool] LBool 1 (HOBool [LArrow LBool LBool] True))
  (HOPOrdinary [LArrow LBool LBool] [LBool] LBool 1 (HOBool [LArrow LBool LBool] False))

alignedIfWitness : HigherOrderPathAlignment Tests.Shadow.alignedIf Tests.Shadow.alignedIf
alignedIfWitness = AlignPathIf (AlignPathAt [LArrow LBool LBool] [LBool] LBool 1 LHere (Var FZ))
  (AlignPathOrdinary (AlignBool [LArrow LBool LBool] True))
  (AlignPathOrdinary (AlignBool [LArrow LBool LBool] False))

alignedIfTrue : applyMorphism (dependentPathSemantics Tests.Shadow.alignedIf (\_ => (True, False)))
  ((Tests.Shadow.setoidIdentity, ()), (Tests.Shadow.alignedEnvPath1, ())) = True
alignedIfTrue = trans (dependentPathAlignedRelated Tests.Shadow.alignedIfWitness (\_ => (True, False))
  ((Tests.Shadow.setoidIdentity, ()), (Tests.Shadow.alignedEnvPath1, ()))
  ((Tests.Shadow.setoidConditionalIdentity, ()), (Tests.Shadow.alignedEnvPath2, ()))
  ((Tests.Shadow.setoidIdentityEquivalent, Refl), Tests.Shadow.alignedEnvPathRelated)) Refl

alignedIfFalse : applyMorphism (dependentPathSemantics Tests.Shadow.alignedIf (\_ => (False, True)))
  ((Tests.Shadow.setoidIdentity, ()), (Tests.Shadow.alignedEnvPath1, ())) = False
alignedIfFalse = trans (dependentPathAlignedRelated Tests.Shadow.alignedIfWitness (\_ => (False, True))
  ((Tests.Shadow.setoidIdentity, ()), (Tests.Shadow.alignedEnvPath1, ()))
  ((Tests.Shadow.setoidConditionalIdentity, ()), (Tests.Shadow.alignedEnvPath2, ()))
  ((Tests.Shadow.setoidIdentityEquivalent, Refl), Tests.Shadow.alignedEnvPathRelated)) Refl

-- The alignment is checked against the witness extracted from admissibility.
dependentLinearAlignedLeft : (b : Bool) -> dependentFlip b (False, False) =
  applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderLinearIfAgain) (b, ())
dependentLinearAlignedLeft b = dependentDeclaredLeftAlignedAtFace CommonDeclaredHere
  Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible (b, ())
  (\_ => (False, False)) (the (ScopedFace 1) (SEndpoint FZ False)) (Var FZ) Refl Refl
  Tests.Shadow.higherOrderLinearIfAgain Tests.Shadow.higherOrderLinearAlignment

dependentLinearAlignedTrue : dependentFlip True (False, False) = True
dependentLinearAlignedTrue = trans (Tests.Shadow.dependentLinearAlignedLeft True) Refl

dependentLinearAlignedFalse : dependentFlip False (False, False) = False
dependentLinearAlignedFalse = trans (Tests.Shadow.dependentLinearAlignedLeft False) Refl

dependentTailAlignedRight : applyMorphism Tests.Shadow.dependentTailPath ((), (True, True)) = True
dependentTailAlignedRight = dependentDeclaredRightAlignedAtFace (CommonDeclaredThere CommonDeclaredHere)
  Tests.Shadow.dependentTwoPaths Tests.Shadow.dependentTwoAdmissible () (\_ => (True, True))
  (the (ScopedFace 1) (SEndpoint FZ True)) (Var FZ) Refl Refl (HOBool [] True) (AlignBool [] True)

-- The face derivation is indexed by the actual linear-source typing proof.
dependentLinearReflEvidence : DependentFaceEvidence
  {decls = Tests.Shadow.dependentLinearDeclarations} {face = the (ScopedFace 1) STop}
  (CommonRefl (CPOrdinaryType (sourceCommonTyped Tests.Shadow.linearSource)))
  Tests.Shadow.pathLinearIf Tests.Shadow.pathLinearIf
dependentLinearReflEvidence = DepFaceRefl Tests.Shadow.pathLinearAlignment

dependentLinearCompositeEvidence : DependentFaceEvidence
  {decls = Tests.Shadow.dependentLinearDeclarations} {face = the (ScopedFace 1) STop}
  (CommonTrans (CommonSym (CommonRefl (CPOrdinaryType (sourceCommonTyped Tests.Shadow.linearSource))))
    (CommonRefl (CPOrdinaryType (sourceCommonTyped Tests.Shadow.linearSource))))
  Tests.Shadow.pathLinearIf Tests.Shadow.pathLinearIf
dependentLinearCompositeEvidence = DepFaceTrans (DepFaceSym Tests.Shadow.dependentLinearReflEvidence)
  Tests.Shadow.pathLinearAlignment Tests.Shadow.dependentLinearReflEvidence

dependentLinearRestrictedEvidence : DependentFaceEvidence
  {decls = Tests.Shadow.dependentLinearDeclarations} {face = the (ScopedFace 1) (SEndpoint FZ False)}
  (CommonRestrict {source = STop} (CommonTrans (CommonSym (CommonRefl (CPOrdinaryType (sourceCommonTyped Tests.Shadow.linearSource))))
    (CommonRefl (CPOrdinaryType (sourceCommonTyped Tests.Shadow.linearSource)))) Refl)
  Tests.Shadow.pathLinearIf Tests.Shadow.pathLinearIf
dependentLinearRestrictedEvidence = DepFaceRestrict (SEndpoint FZ False) STop Refl Tests.Shadow.dependentLinearCompositeEvidence

dependentLinearCompositeSound : (b : Bool) ->
  applyMorphism (dependentPathSemantics Tests.Shadow.pathLinearIf (\_ => (True, False)))
    ((b, ()), Tests.Shadow.dependentLinearPaths) =
  applyMorphism (dependentPathSemantics Tests.Shadow.pathLinearIf (\_ => (True, False)))
    ((b, ()), Tests.Shadow.dependentLinearPaths)
dependentLinearCompositeSound b = dependentFaceEvidenceSound Tests.Shadow.dependentLinearCompositeEvidence
  (b, ()) Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible (\_ => (True, False)) Refl

dependentLinearRestrictedSound : (b : Bool) ->
  applyMorphism (dependentPathSemantics Tests.Shadow.pathLinearIf (\_ => (False, False)))
    ((b, ()), Tests.Shadow.dependentLinearPaths) =
  applyMorphism (dependentPathSemantics Tests.Shadow.pathLinearIf (\_ => (False, False)))
    ((b, ()), Tests.Shadow.dependentLinearPaths)
dependentLinearRestrictedSound b = dependentFaceEvidenceSound Tests.Shadow.dependentLinearRestrictedEvidence
  (b, ()) Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible (\_ => (False, False)) Refl

-- This face proof interprets the named path, not the ordinary endpoint.
dependentAtFaceEvidence : DependentFaceEvidence
  {decls = Tests.Shadow.dependentLinearDeclarations} {face = the (ScopedFace 1) STop}
  (CommonRefl (CPAtType {i = Var FZ} LHere))
  Tests.Shadow.dependentLinearAt Tests.Shadow.dependentLinearAt
dependentAtFaceEvidence = DepFaceRefl (AlignPathAt [LBool] [LBool] LBool 1 LHere (Var FZ))

dependentAtNonBooleanSound : applyMorphism (dependentPathSemantics Tests.Shadow.dependentLinearAt (\_ => (True, False)))
  ((False, ()), Tests.Shadow.dependentLinearPaths) = True
dependentAtNonBooleanSound = trans (dependentFaceEvidenceSound Tests.Shadow.dependentAtFaceEvidence
  (False, ()) Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible
  (\_ => (True, False)) Refl) Refl

dependentAtEndpointDiffers : applyMorphism (dependentPathSemantics Tests.Shadow.dependentLinearAt (\_ => (False, False)))
  ((False, ()), Tests.Shadow.dependentLinearPaths) = False
dependentAtEndpointDiffers = Refl

dependentLinearEndpointEvidence : DependentEndpointFaceEvidence
  Tests.Shadow.commonLinearIfEndpoint Tests.Shadow.dependentLinearAt Tests.Shadow.pathLinearIf
  Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible
dependentLinearEndpointEvidence = DepEndpointLeft LHere (Var FZ) Tests.Shadow.higherOrderLinearIf
  CommonDeclaredHere Refl Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible
  (\env, valuation, holds => Tests.Shadow.higherOrderLinearAlignment)

dependentLinearEndpointSound : (b : Bool) ->
  applyMorphism (dependentPathSemantics Tests.Shadow.dependentLinearAt (\_ => (False, False)))
    ((b, ()), Tests.Shadow.dependentLinearPaths) =
  applyMorphism (dependentPathSemantics Tests.Shadow.pathLinearIf (\_ => (False, False)))
    ((b, ()), Tests.Shadow.dependentLinearPaths)
dependentLinearEndpointSound b = dependentEndpointFaceEvidenceSound Tests.Shadow.dependentLinearEndpointEvidence
  (b, ()) (\_ => (False, False)) Refl

dependentTailRightEvidence : DependentEndpointFaceEvidence
  {decls = Tests.Shadow.dependentTwoDeclarations} {face = the (ScopedFace 1) (SEndpoint FZ True)}
  (CommonRight {i = Var FZ} (CommonDeclaredThere CommonDeclaredHere) Refl)
  (HOPAt [] [LBool, LBool] LBool 1 (LThere LHere) (Var FZ))
  (HOPOrdinary [] [LBool, LBool] LBool 1 (HOBool [] True))
  Tests.Shadow.dependentTwoPaths Tests.Shadow.dependentTwoAdmissible
dependentTailRightEvidence = DepEndpointRight (LThere LHere) (Var FZ) (HOBool [] True)
  (CommonDeclaredThere CommonDeclaredHere) Refl Tests.Shadow.dependentTwoPaths Tests.Shadow.dependentTwoAdmissible
  (\env, valuation, holds => AlignBool [] True)

dependentTailRightSound : applyMorphism Tests.Shadow.dependentTailPath ((), (True, True)) = True
dependentTailRightSound = dependentEndpointFaceEvidenceSound Tests.Shadow.dependentTailRightEvidence () (\_ => (True, True)) Refl

dependentLinearTwoDimEvidence : DependentEndpointFaceEvidence
  {decls = Tests.Shadow.dependentLinearDeclarations} {face = the (ScopedFace 2) (SEndpoint FZ False)}
  (CommonLeft {i = Var FZ} CommonDeclaredHere Refl)
  (HOPAt [LBool] [LBool] LBool 2 LHere (Var FZ))
  (HOPOrdinary [LBool] [LBool] LBool 2 Tests.Shadow.higherOrderLinearIf)
  Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible
dependentLinearTwoDimEvidence = DepEndpointLeft LHere (Var FZ) Tests.Shadow.higherOrderLinearIf
  CommonDeclaredHere Refl Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible
  (\env, valuation, holds => Tests.Shadow.higherOrderLinearAlignment)

dependentLinearUnrelatedNonBoolean : (b : Bool) ->
  applyMorphism (dependentPathSemantics (HOPAt [LBool] [LBool] LBool 2 LHere (Var FZ))
    (\i => case i of FZ => (False, False); FS FZ => (True, False))) ((b, ()), Tests.Shadow.dependentLinearPaths) =
  applyMorphism (higherOrderTermSemantics Tests.Shadow.higherOrderLinearIf) (b, ())
dependentLinearUnrelatedNonBoolean b = dependentEndpointFaceEvidenceSound Tests.Shadow.dependentLinearTwoDimEvidence
  (b, ()) (\i => case i of FZ => (False, False); FS FZ => (True, False)) Refl

dependentLinearEndpointRestricted : DependentEndpointFaceEvidence
  {decls = Tests.Shadow.dependentLinearDeclarations} {face = the (ScopedFace 1) (SEndpoint FZ False)}
  (CommonRestrict {source = SEndpoint FZ False} Tests.Shadow.commonLinearIfEndpoint Refl)
  Tests.Shadow.dependentLinearAt Tests.Shadow.pathLinearIf Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible
dependentLinearEndpointRestricted = DepEndpointRestrict (SEndpoint FZ False) (SEndpoint FZ False) Refl Tests.Shadow.dependentLinearEndpointEvidence

-- Symmetry and transitivity are used on endpoint evidence, not just reflexivity.
dependentLinearEndpointRoundTrip : DependentEndpointFaceEvidence
  (CommonTrans (CommonSym Tests.Shadow.commonLinearIfEndpoint) Tests.Shadow.commonLinearIfEndpoint)
  Tests.Shadow.pathLinearIf Tests.Shadow.pathLinearIf
  Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible
dependentLinearEndpointRoundTrip = DepEndpointTrans (DepEndpointSym Tests.Shadow.dependentLinearEndpointEvidence)
  (AlignPathAt [LBool] [LBool] LBool 1 LHere (Var FZ)) Tests.Shadow.dependentLinearEndpointEvidence

dependentLinearEndpointRoundTripConsumed : (b : Bool) ->
  applyMorphism (dependentPathSemantics Tests.Shadow.pathLinearIf (\_ => (False, False)))
    ((b, ()), Tests.Shadow.dependentLinearPaths) = b
dependentLinearEndpointRoundTripConsumed b = trans
  (dependentEndpointFaceEvidenceSound Tests.Shadow.dependentLinearEndpointRoundTrip
    (b, ()) (\_ => (False, False)) Refl) (sym (Tests.Shadow.dependentLinearEndpoint b))

dependentLinearThreeDimEvidence : DependentEndpointFaceEvidence
  {decls = Tests.Shadow.dependentLinearDeclarations} {face = the (ScopedFace 3) (SEndpoint FZ False)}
  (CommonLeft {i = Var FZ} CommonDeclaredHere Refl)
  (HOPAt [LBool] [LBool] LBool 3 LHere (Var FZ))
  (HOPOrdinary [LBool] [LBool] LBool 3 Tests.Shadow.higherOrderLinearIf)
  Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible
dependentLinearThreeDimEvidence = DepEndpointLeft LHere (Var FZ) Tests.Shadow.higherOrderLinearIf
  CommonDeclaredHere Refl Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible
  (\env, valuation, holds => Tests.Shadow.higherOrderLinearAlignment)

dependentLinearStrictRestriction : DependentEndpointFaceEvidence
  {decls = Tests.Shadow.dependentLinearDeclarations}
  {face = the (ScopedFace 3) (SConjunction (SEndpoint FZ False) (SEndpoint (FS FZ) True))}
  (CommonRestrict {source = SEndpoint FZ False} (CommonLeft {i = Var FZ} CommonDeclaredHere Refl) Refl)
  (HOPAt [LBool] [LBool] LBool 3 LHere (Var FZ))
  (HOPOrdinary [LBool] [LBool] LBool 3 Tests.Shadow.higherOrderLinearIf)
  Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible
dependentLinearStrictRestriction = DepEndpointRestrict
  (SConjunction (SEndpoint FZ False) (SEndpoint (FS FZ) True)) (SEndpoint FZ False) Refl
  Tests.Shadow.dependentLinearThreeDimEvidence

dependentLinearStrictRestrictionConsumed : (b : Bool) ->
  applyMorphism (dependentPathSemantics (HOPAt [LBool] [LBool] LBool 3 LHere (Var FZ))
    (\i => case i of FZ => (False, False); FS FZ => (True, True); FS (FS FZ) => (True, False)))
    ((b, ()), Tests.Shadow.dependentLinearPaths) = b
dependentLinearStrictRestrictionConsumed b = trans
  (dependentEndpointFaceEvidenceSound Tests.Shadow.dependentLinearStrictRestriction (b, ())
    (\i => case i of FZ => (False, False); FS FZ => (True, True); FS (FS FZ) => (True, False)) Refl)
  (sym (Tests.Shadow.dependentLinearEndpoint b))

dependentLinearEndpointSymConsumed : (b : Bool) ->
  applyMorphism (dependentPathSemantics Tests.Shadow.pathLinearIf (\_ => (False, False)))
    ((b, ()), Tests.Shadow.dependentLinearPaths) = b
dependentLinearEndpointSymConsumed b = trans
  (dependentEndpointFaceEvidenceSound (DepEndpointSym Tests.Shadow.dependentLinearEndpointEvidence)
    (b, ()) (\_ => (False, False)) Refl) Refl

-- The source holds while the conjunction fails, so this restriction is strict.
dependentLinearRestrictionIsStrict :
  (faceAtVal (\_ => (False, False)) (the (ScopedFace 3) (SEndpoint FZ False)),
   faceAtVal (\_ => (False, False))
     (the (ScopedFace 3) (SConjunction (SEndpoint FZ False) (SEndpoint (FS FZ) True)))) = (True, False)
dependentLinearRestrictionIsStrict = Refl

-- Congruence consumes the actual endpoint derivations in every conditional slot.
dependentEndpointIfEvidence : DependentEndpointFaceEvidence
  (CommonIfEqual Tests.Shadow.commonLinearIfEndpoint Tests.Shadow.commonLinearIfEndpoint Tests.Shadow.commonLinearIfEndpoint)
  (HOPIf [LBool] [LBool] LBool 1 Tests.Shadow.dependentLinearAt Tests.Shadow.dependentLinearAt Tests.Shadow.dependentLinearAt)
  (HOPIf [LBool] [LBool] LBool 1 Tests.Shadow.pathLinearIf Tests.Shadow.pathLinearIf Tests.Shadow.pathLinearIf)
  Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible
dependentEndpointIfEvidence = DepEndpointIf Tests.Shadow.dependentLinearEndpointEvidence
  Tests.Shadow.dependentLinearEndpointEvidence Tests.Shadow.dependentLinearEndpointEvidence

dependentEndpointIfSound : (b : Bool) ->
  applyMorphism (dependentPathSemantics (HOPIf [LBool] [LBool] LBool 1 Tests.Shadow.dependentLinearAt Tests.Shadow.dependentLinearAt Tests.Shadow.dependentLinearAt) (\_ => (False, False)))
    ((b, ()), Tests.Shadow.dependentLinearPaths) =
  applyMorphism (dependentPathSemantics (HOPIf [LBool] [LBool] LBool 1 Tests.Shadow.pathLinearIf Tests.Shadow.pathLinearIf Tests.Shadow.pathLinearIf) (\_ => (False, False)))
    ((b, ()), Tests.Shadow.dependentLinearPaths)
dependentEndpointIfSound b = dependentEndpointFaceEvidenceSound Tests.Shadow.dependentEndpointIfEvidence (b, ()) (\_ => (False, False)) Refl

-- The lambda ignores its Unit argument and returns the environment's value.
congruenceApplicationEvidence : (a : LogicalType) -> DependentEndpointFaceEvidence
  {decls = CommonNoPaths} {face = the (ScopedFace 0) STop}
  (CommonAppEqual (CommonRefl (CPLamType (CPOrdinaryType (CVariable (LThere LHere)))))
                  (CommonRefl (CPOrdinaryType CUnitType)))
  (HOPApplication [a] [] LUnit a 0
    (HOPLambda [a] [] LUnit a 0 (HOPOrdinary [LUnit, a] [] a 0 (HOVar [LUnit, a] a (LThere LHere))))
    (HOPOrdinary [a] [] LUnit 0 (HOUnit [a])))
  (HOPApplication [a] [] LUnit a 0
    (HOPLambda [a] [] LUnit a 0 (HOPOrdinary [LUnit, a] [] a 0 (HOVar [LUnit, a] a (LThere LHere))))
    (HOPOrdinary [a] [] LUnit 0 (HOUnit [a]))) () DependentAdmissibleNil
congruenceApplicationEvidence a = DepEndpointApp
  (DepEndpointStructural (DepFaceRefl (AlignPathLambda (AlignPathOrdinary (AlignVar [LUnit, a] a (LThere LHere))))))
  (DepEndpointStructural (DepFaceRefl (AlignPathOrdinary (AlignUnit [a]))))

congruenceApplicationSound : (a : LogicalType) -> (v : carrier (commonTypeSetoid a)) ->
  related (commonTypeSetoid a)
    (applyMorphism (dependentPathSemantics (HOPApplication [a] [] LUnit a 0
      (HOPLambda [a] [] LUnit a 0 (HOPOrdinary [LUnit, a] [] a 0 (HOVar [LUnit, a] a (LThere LHere))))
      (HOPOrdinary [a] [] LUnit 0 (HOUnit [a]))) (\_ => (False, False))) ((v, ()), ()))
    (applyMorphism (dependentPathSemantics (HOPApplication [a] [] LUnit a 0
      (HOPLambda [a] [] LUnit a 0 (HOPOrdinary [LUnit, a] [] a 0 (HOVar [LUnit, a] a (LThere LHere))))
      (HOPOrdinary [a] [] LUnit 0 (HOUnit [a]))) (\_ => (False, False))) ((v, ()), ()))
congruenceApplicationSound a v = dependentEndpointFaceEvidenceSound (Tests.Shadow.congruenceApplicationEvidence a) (v, ()) (\_ => (False, False)) Refl

congruenceApplicationUnit : () = ()
congruenceApplicationUnit = congruenceApplicationSound LUnit ()

congruenceApplicationBool : True = True
congruenceApplicationBool = congruenceApplicationSound LBool True

congruenceApplicationArrow : related (commonTypeSetoid (LArrow LBool LBool)) Tests.Shadow.setoidIdentity Tests.Shadow.setoidIdentity
congruenceApplicationArrow = congruenceApplicationSound (LArrow LBool LBool) Tests.Shadow.setoidIdentity

congruenceIfTrue : True = True
congruenceIfTrue = dependentEndpointIfSound True

congruenceIfFalse : False = False
congruenceIfFalse = dependentEndpointIfSound False

pathLinearIfAgain : HigherOrderPathTerm [LBool] [LBool] LBool 1 (CPOrdinaryType (sourceCommonTyped Tests.Shadow.linearSource))
pathLinearIfAgain = HOPOrdinary [LBool] [LBool] LBool 1 Tests.Shadow.higherOrderLinearIfAgain

alignedEndpointEvidence : DependentEndpointFaceEvidence
  Tests.Shadow.commonLinearIfEndpoint Tests.Shadow.dependentLinearAt Tests.Shadow.pathLinearIfAgain
  Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible
alignedEndpointEvidence = DepEndpointAlign (AlignPathAt [LBool] [LBool] LBool 1 LHere (Var FZ))
  Tests.Shadow.dependentLinearEndpointEvidence (AlignPathOrdinary Tests.Shadow.higherOrderLinearAlignment)

unitEndpointEvidence : DependentEndpointFaceEvidence
  (CommonUnitElimEqual (CommonRefl (CPOrdinaryType CUnitType)) Tests.Shadow.commonLinearIfEndpoint)
  (HOPUnitElim [LBool] [LBool] LBool 1 (HOPOrdinary [LBool] [LBool] LUnit 1 (HOUnit [LBool])) Tests.Shadow.dependentLinearAt)
  (HOPUnitElim [LBool] [LBool] LBool 1 (HOPOrdinary [LBool] [LBool] LUnit 1 (HOUnit [LBool])) Tests.Shadow.pathLinearIfAgain)
  Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible
unitEndpointEvidence = DepEndpointUnitElim
  (DepEndpointStructural (DepFaceRefl (AlignPathOrdinary (AlignUnit [LBool])))) Tests.Shadow.alignedEndpointEvidence

unitEndpointSound : (b : Bool) ->
  applyMorphism (dependentPathSemantics (HOPUnitElim [LBool] [LBool] LBool 1 (HOPOrdinary [LBool] [LBool] LUnit 1 (HOUnit [LBool])) Tests.Shadow.dependentLinearAt) (\_ => (False, False))) ((b, ()), Tests.Shadow.dependentLinearPaths) =
  applyMorphism (dependentPathSemantics (HOPUnitElim [LBool] [LBool] LBool 1 (HOPOrdinary [LBool] [LBool] LUnit 1 (HOUnit [LBool])) Tests.Shadow.pathLinearIfAgain) (\_ => (False, False))) ((b, ()), Tests.Shadow.dependentLinearPaths)
unitEndpointSound b = dependentEndpointFaceEvidenceSound Tests.Shadow.unitEndpointEvidence (b, ()) (\_ => (False, False)) Refl

nonBooleanApplicationEvidence : DependentEndpointFaceEvidence
  {decls = Tests.Shadow.dependentLinearDeclarations} {face = the (ScopedFace 1) STop}
  (CommonAppEqual (CommonRefl (CPLamType (CPAtType {i = Var FZ} LHere))) (CommonRefl (CPAtType {i = Var FZ} LHere)))
  (HOPApplication [LBool] [LBool] LBool LBool 1 Tests.Shadow.dependentBinder Tests.Shadow.dependentLinearAt)
  (HOPApplication [LBool] [LBool] LBool LBool 1 Tests.Shadow.dependentBinder Tests.Shadow.dependentLinearAt)
  Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible
nonBooleanApplicationEvidence = DepEndpointApp
  (DepEndpointStructural (DepFaceRefl (AlignPathLambda (AlignPathAt [LBool, LBool] [LBool] LBool 1 LHere (Var FZ)))))
  (DepEndpointStructural (DepFaceRefl (AlignPathAt [LBool] [LBool] LBool 1 LHere (Var FZ))))

nonBooleanApplicationSound :
  applyMorphism (dependentPathSemantics (HOPApplication [LBool] [LBool] LBool LBool 1 Tests.Shadow.dependentBinder Tests.Shadow.dependentLinearAt) (\_ => (True, False)))
    ((False, ()), Tests.Shadow.dependentLinearPaths) = True
nonBooleanApplicationSound = trans (dependentEndpointFaceEvidenceSound Tests.Shadow.nonBooleanApplicationEvidence
  (False, ()) (\_ => (True, False)) Refl) Refl

-- Compose the congruence theorem with the ordinary environment's extensional
-- relation, without requiring equality of the two function values.
congruenceApplicationDistinctEnvironments : related (commonTypeSetoid (LArrow LBool LBool))
  (applyMorphism (dependentPathSemantics (HOPApplication [LArrow LBool LBool] [] LUnit (LArrow LBool LBool) 0
    (HOPLambda [LArrow LBool LBool] [] LUnit (LArrow LBool LBool) 0
      (HOPOrdinary [LUnit, LArrow LBool LBool] [] (LArrow LBool LBool) 0 (HOVar [LUnit, LArrow LBool LBool] (LArrow LBool LBool) (LThere LHere))))
    (HOPOrdinary [LArrow LBool LBool] [] LUnit 0 (HOUnit [LArrow LBool LBool]))) (\_ => (False, False))) ((Tests.Shadow.setoidIdentity, ()), ()))
  (applyMorphism (dependentPathSemantics (HOPApplication [LArrow LBool LBool] [] LUnit (LArrow LBool LBool) 0
    (HOPLambda [LArrow LBool LBool] [] LUnit (LArrow LBool LBool) 0
      (HOPOrdinary [LUnit, LArrow LBool LBool] [] (LArrow LBool LBool) 0 (HOVar [LUnit, LArrow LBool LBool] (LArrow LBool LBool) (LThere LHere))))
    (HOPOrdinary [LArrow LBool LBool] [] LUnit 0 (HOUnit [LArrow LBool LBool]))) (\_ => (False, False))) ((Tests.Shadow.setoidConditionalIdentity, ()), ()))
congruenceApplicationDistinctEnvironments x y xy = trans
  (Tests.Shadow.congruenceApplicationSound (LArrow LBool LBool) Tests.Shadow.setoidIdentity x x Refl)
  (Tests.Shadow.setoidIdentityEquivalent x y xy)

-- The branches differ observably; the condition is the declared path endpoint.
dependentEndpointChoiceEvidence : DependentEndpointFaceEvidence
  (CommonIfEqual Tests.Shadow.commonLinearIfEndpoint
    (CommonRefl (CPOrdinaryType (CBoolType {b = True})))
    (CommonRefl (CPOrdinaryType (CBoolType {b = False}))))
  (HOPIf [LBool] [LBool] LBool 1 Tests.Shadow.dependentLinearAt
    (HOPOrdinary [LBool] [LBool] LBool 1 (HOBool [LBool] True))
    (HOPOrdinary [LBool] [LBool] LBool 1 (HOBool [LBool] False)))
  (HOPIf [LBool] [LBool] LBool 1 Tests.Shadow.pathLinearIf
    (HOPOrdinary [LBool] [LBool] LBool 1 (HOBool [LBool] True))
    (HOPOrdinary [LBool] [LBool] LBool 1 (HOBool [LBool] False)))
  Tests.Shadow.dependentLinearPaths Tests.Shadow.dependentLinearAdmissible
dependentEndpointChoiceEvidence = DepEndpointIf Tests.Shadow.dependentLinearEndpointEvidence
  (DepEndpointStructural (DepFaceRefl (AlignPathOrdinary (AlignBool [LBool] True))))
  (DepEndpointStructural (DepFaceRefl (AlignPathOrdinary (AlignBool [LBool] False))))

dependentEndpointChoiceTrue :
  applyMorphism (dependentPathSemantics (HOPIf [LBool] [LBool] LBool 1 Tests.Shadow.dependentLinearAt
    (HOPOrdinary [LBool] [LBool] LBool 1 (HOBool [LBool] True))
    (HOPOrdinary [LBool] [LBool] LBool 1 (HOBool [LBool] False))) (\_ => (False, False)))
    ((True, ()), Tests.Shadow.dependentLinearPaths) = True
dependentEndpointChoiceTrue = trans (dependentEndpointFaceEvidenceSound Tests.Shadow.dependentEndpointChoiceEvidence
  (True, ()) (\_ => (False, False)) Refl) Refl

dependentEndpointChoiceFalse :
  applyMorphism (dependentPathSemantics (HOPIf [LBool] [LBool] LBool 1 Tests.Shadow.dependentLinearAt
    (HOPOrdinary [LBool] [LBool] LBool 1 (HOBool [LBool] True))
    (HOPOrdinary [LBool] [LBool] LBool 1 (HOBool [LBool] False))) (\_ => (False, False)))
    ((False, ()), Tests.Shadow.dependentLinearPaths) = False
dependentEndpointChoiceFalse = trans (dependentEndpointFaceEvidenceSound Tests.Shadow.dependentEndpointChoiceEvidence
  (False, ()) (\_ => (False, False)) Refl) Refl

-- Dimension weakening keeps non-Boolean older observations and ambient faces.
commonWeakeningNonBoolean :
  evalDMVal (extendCommonValuation (False, False) (\_ => (True, False)))
    (weakenInterval (Meet (Var FZ) (Reverse (Var FZ)))) = (True, False)
commonWeakeningNonBoolean = commonIntervalWeakeningVal (False, False) (the (Fin 1 -> DM) (\_ => (True, False)))
  (Meet (Var FZ) (Reverse (Var FZ)))

commonWeakeningEndpointTrue :
  faceAtVal (extendCommonValuation (True, True) (\_ => (True, False)))
    (SConjunction (weakenFace (the (ScopedFace 1) (SEndpoint FZ False))) (SEndpoint FZ True)) = False
commonWeakeningEndpointTrue = Refl

commonWeakeningEndpointHolds : (side : Bool) ->
  faceAtVal (extendCommonValuation (side, side) (\_ => (True, False)))
    (SConjunction (weakenFace (the (ScopedFace 1) STop)) (SEndpoint FZ side)) = True
commonWeakeningEndpointHolds side = commonEndpointFaceHolds side (the (Fin 1 -> DM) (\_ => (True, False))) STop Refl

-- Valuation congruence traverses the lambda and a dependent named path.
dependentBinderValuationCongruence : related (commonTypeSetoid (LArrow LBool LBool))
  (applyMorphism (dependentPathSemantics Tests.Shadow.dependentBinder (\_ => (True, False)))
    ((False, ()), Tests.Shadow.dependentLinearPaths))
  (applyMorphism (dependentPathSemantics Tests.Shadow.dependentBinder (\_ => (True, False)))
    ((False, ()), (Tests.Shadow.dependentLinearPathAlternative, ())))
dependentBinderValuationCongruence = dependentPathValuationCongruence Tests.Shadow.dependentBinder
  (\_ => (True, False)) (\_ => (True, False)) (\_ => Refl)
  ((False, ()), Tests.Shadow.dependentLinearPaths)
  ((False, ()), (Tests.Shadow.dependentLinearPathAlternative, ()))
  ((Refl, Refl), Tests.Shadow.dependentLinearPathsRelated)
