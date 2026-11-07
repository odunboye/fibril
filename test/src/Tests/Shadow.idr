module Tests.Shadow

import Data.Vect
import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Usage
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.OpenPath

import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Foundation.DeMorgan.Face


import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Quantitative.Usage

import Fibril.Core.Quantitative.Substitution
import Fibril.Cubical.Logical.ShadowSubstitution
import Fibril.Cubical.Logical.ShadowPath
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
