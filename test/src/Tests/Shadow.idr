module Tests.Shadow

import Data.Vect
import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Quantitative.Syntax
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
