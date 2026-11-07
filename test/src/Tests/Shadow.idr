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
