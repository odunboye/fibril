module Tests.Cubical.ScopedSyntax

import Data.Fin
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Interval

%default total

-- Arbitrarily high candidate paths, not a claim that they type-check.
higherTerm : Nat -> Expr 1 0
higherTerm Z = Variable FZ
higherTerm (S k) = Abstract (weakenDimensions (higherTerm k))

higherType : Nat -> Expr 1 0
higherType Z = Variable FZ
higherType (S k) = Path (weakenDimensions (higherType k)) (higherTerm k) (higherTerm k)

termCaptureAvoided : substituteTerms (\_ => Apply (Variable FZ) (Var FZ))
  (Abstract (Variable FZ) {m = 1} {n = 1}) =
  Abstract (Apply (Variable FZ) (Var (FS FZ)))
termCaptureAvoided = Refl

dimensionCaptureAvoided : substituteDimensions (\_ => Var FZ)
  (Abstract (Apply (Variable FZ) (Var (FS FZ))) {m = 1} {n = 1}) =
  Abstract (Apply (Variable FZ) (Var (FS FZ)))
dimensionCaptureAvoided = Refl

termIdentityExample : substituteTerms Variable (higherType 4) = higherType 4
termIdentityExample = termIdentity (higherType 4)

dimensionIdentityExample : substituteDimensions Var (higherType 4) = higherType 4
dimensionIdentityExample = dimensionIdentity (higherType 4)

-- The family sees a fresh FZ; the same outer variable is FS FZ there,
-- but FZ in both endpoints. Its replacement must be weakened only in the family.
familyAndEndpoints : Expr 1 1
familyAndEndpoints = Path
  (Apply (Variable FZ) (Meet (Var FZ) (Var (FS FZ))))
  (Apply (Variable FZ) (Var FZ))
  (Apply (Variable FZ) (Reverse (Var FZ)))

familyAndEndpointsSubstitution :
  substituteDimensions (\_ => Reverse (Var FZ)) Tests.Cubical.ScopedSyntax.familyAndEndpoints =
  Path (Apply (Variable FZ) (Meet (Var FZ) (Reverse (Var (FS FZ)))))
       (Apply (Variable FZ) (Reverse (Var FZ)))
       (Apply (Variable FZ) (Reverse (Reverse (Var FZ))))
familyAndEndpointsSubstitution = Refl

swapAndExpand : Fin 2 -> ScopedInterval 2
swapAndExpand FZ = Var (FS FZ)
swapAndExpand (FS FZ) = Meet (Var FZ) One

-- Both bound variables stay fixed; both outer variables are substituted at
-- once, and the replacements' free variables shift past both binders.
nestedDimensions : Expr 1 2
nestedDimensions = Abstract (Abstract (Apply (Variable FZ)
  (Meet (Meet (Var FZ) (Var (FS FZ)))
        (Meet (Var (FS (FS FZ))) (Var (FS (FS (FS FZ))))))))

nestedSimultaneousDimensions : substituteDimensions Tests.Cubical.ScopedSyntax.swapAndExpand Tests.Cubical.ScopedSyntax.nestedDimensions =
  Abstract (Abstract (Apply (Variable FZ)
    (Meet (Meet (Var FZ) (Var (FS FZ)))
          (Meet (Var (FS (FS (FS FZ)))) (Meet (Var (FS (FS FZ))) One)))))
nestedSimultaneousDimensions = Refl

replaceBoth : Fin 2 -> Expr 2 1
replaceBoth FZ = Apply (Variable (FS FZ)) (Var FZ)
replaceBoth (FS FZ) = Apply (Variable FZ) (Reverse (Var FZ))

-- This also checks simultaneous term substitution: the variables inside the
-- replacement expressions are not recursively substituted. Both replacement
-- dimensions must remain outer after traversing the two abstractions.
nestedTermVariables : Expr 2 1
nestedTermVariables = Abstract (Abstract
  (Apply (Apply (Variable FZ) (Var FZ)) (Var (FS FZ))))

nestedTermReplacement : substituteTerms Tests.Cubical.ScopedSyntax.replaceBoth Tests.Cubical.ScopedSyntax.nestedTermVariables =
  Abstract (Abstract
    (Apply (Apply (Apply (Variable (FS FZ)) (Var (FS (FS FZ)))) (Var FZ)) (Var (FS FZ))))
nestedTermReplacement = Refl

bothTermVariables : Expr 2 1
bothTermVariables = Path (Variable FZ) (Variable FZ) (Variable (FS FZ))

simultaneousTermReplacement : substituteTerms Tests.Cubical.ScopedSyntax.replaceBoth Tests.Cubical.ScopedSyntax.bothTermVariables =
  Path (Apply (Variable (FS FZ)) (Var (FS FZ)))
       (Apply (Variable (FS FZ)) (Var FZ))
       (Apply (Variable FZ) (Reverse (Var FZ)))
simultaneousTermReplacement = Refl

-- A family under Path and Abstract sees two fresh indices; endpoints see only
-- the outer index. Both substitution environments are deliberately nonidentity.
nestedPath : Expr 2 1
nestedPath = Path
  (Abstract (Apply (Variable FZ) (Meet (Var FZ) (Var (FS (FS FZ))))))
  (Variable (FS FZ))
  (Apply (Variable FZ) (Var FZ))

reverseDimension : Fin 1 -> ScopedInterval 1
reverseDimension FZ = Reverse (Var FZ)

closeDimension : Fin 1 -> ScopedInterval 0
closeDimension FZ = One

nestedDimensionComposition :
  substituteDimensions Tests.Cubical.ScopedSyntax.closeDimension
    (substituteDimensions Tests.Cubical.ScopedSyntax.reverseDimension Tests.Cubical.ScopedSyntax.nestedPath) =
  Path (Abstract (Apply (Variable FZ) (Meet (Var FZ) (Reverse One))))
       (Variable (FS FZ)) (Apply (Variable FZ) (Reverse One))
nestedDimensionComposition = Refl

nestedDimensionCompositionLaw :
  substituteDimensions Tests.Cubical.ScopedSyntax.closeDimension
    (substituteDimensions Tests.Cubical.ScopedSyntax.reverseDimension Tests.Cubical.ScopedSyntax.nestedPath) =
  substituteDimensions (substituteScoped Tests.Cubical.ScopedSyntax.closeDimension . Tests.Cubical.ScopedSyntax.reverseDimension) Tests.Cubical.ScopedSyntax.nestedPath
nestedDimensionCompositionLaw = dimensionSubstitutionComposition Tests.Cubical.ScopedSyntax.reverseDimension Tests.Cubical.ScopedSyntax.closeDimension Tests.Cubical.ScopedSyntax.nestedPath

nestedTermCompositionLaw :
  substituteTerms Tests.Cubical.ScopedSyntax.replaceBoth
    (substituteTerms Tests.Cubical.ScopedSyntax.replaceBoth Tests.Cubical.ScopedSyntax.nestedPath) =
  substituteTerms (substituteTerms Tests.Cubical.ScopedSyntax.replaceBoth . Tests.Cubical.ScopedSyntax.replaceBoth) Tests.Cubical.ScopedSyntax.nestedPath
nestedTermCompositionLaw = termSubstitutionComposition Tests.Cubical.ScopedSyntax.replaceBoth Tests.Cubical.ScopedSyntax.replaceBoth Tests.Cubical.ScopedSyntax.nestedPath

nestedInteractionLaw :
  substituteDimensions Tests.Cubical.ScopedSyntax.reverseDimension
    (substituteTerms Tests.Cubical.ScopedSyntax.replaceBoth Tests.Cubical.ScopedSyntax.nestedPath) =
  substituteTerms (substituteDimensions Tests.Cubical.ScopedSyntax.reverseDimension . Tests.Cubical.ScopedSyntax.replaceBoth)
    (substituteDimensions Tests.Cubical.ScopedSyntax.reverseDimension Tests.Cubical.ScopedSyntax.nestedPath)
nestedInteractionLaw = termDimensionSubstitution Tests.Cubical.ScopedSyntax.replaceBoth Tests.Cubical.ScopedSyntax.reverseDimension Tests.Cubical.ScopedSyntax.nestedPath

nestedInteractionResult :
  substituteDimensions Tests.Cubical.ScopedSyntax.reverseDimension
    (substituteTerms Tests.Cubical.ScopedSyntax.replaceBoth Tests.Cubical.ScopedSyntax.nestedPath) =
  Path (Abstract (Apply (Apply (Variable (FS FZ)) (Reverse (Var (FS (FS FZ)))))
                        (Meet (Var FZ) (Reverse (Var (FS (FS FZ)))))))
       (Apply (Variable FZ) (Reverse (Reverse (Var FZ))))
       (Apply (Apply (Variable (FS FZ)) (Reverse (Var FZ))) (Reverse (Var FZ)))
nestedInteractionResult = Refl

swapTerms : Fin 2 -> Fin 2
swapTerms FZ = FS FZ
swapTerms (FS FZ) = FZ

nestedRenameDimensionLaw :
  renameTerms Tests.Cubical.ScopedSyntax.swapTerms
    (substituteDimensions Tests.Cubical.ScopedSyntax.reverseDimension Tests.Cubical.ScopedSyntax.nestedPath) =
  substituteDimensions Tests.Cubical.ScopedSyntax.reverseDimension
    (renameTerms Tests.Cubical.ScopedSyntax.swapTerms Tests.Cubical.ScopedSyntax.nestedPath)
nestedRenameDimensionLaw = renameTermsDimensionSubstitution Tests.Cubical.ScopedSyntax.swapTerms Tests.Cubical.ScopedSyntax.reverseDimension Tests.Cubical.ScopedSyntax.nestedPath

nestedRenameResult :
  renameTerms Tests.Cubical.ScopedSyntax.swapTerms Tests.Cubical.ScopedSyntax.nestedPath =
  Path (Abstract (Apply (Variable (FS FZ)) (Meet (Var FZ) (Var (FS (FS FZ))))))
       (Variable FZ) (Apply (Variable (FS FZ)) (Var FZ))
nestedRenameResult = Refl
