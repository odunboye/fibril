module Tests.Renaming

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Renaming

%default total

-- Deliberately scoped, not claimed well typed: proofs apply to raw syntax.
-- Includes every constructor, annotations, nested binders, and outer references.
sample : Term 2
sample =
  Pi Erased (Universe 0)
    (Lambda Linear (Variable FZ)
      (BoolCase BoolTrue
        (Apply (Variable (FS (FS FZ)))
               (UnitCase UnitValue (Variable (FS (FS (FS FZ))))))
        (BoolCase BoolFalse
          (Pi Unrestricted UnitType BoolType)
          (Variable FZ))))

collapse : Fin 2 -> Fin 1
collapse _ = FZ

swap : Fin 2 -> Fin 2
swap FZ = FS FZ
swap (FS FZ) = FZ

-- These declarations check the public theorem signatures in concrete contexts.
identityEvidence : rename Prelude.id Tests.Renaming.sample = Tests.Renaming.sample
identityEvidence = renameIdentity sample

compositionEvidence :
  rename FS (rename Tests.Renaming.collapse Tests.Renaming.sample) =
    rename (FS . Tests.Renaming.collapse) Tests.Renaming.sample
compositionEvidence = renameComposition collapse FS sample

congruenceEvidence :
  rename (\i => Tests.Renaming.swap i) Tests.Renaming.sample =
    rename Tests.Renaming.swap Tests.Renaming.sample
congruenceEvidence = renameCongruent (\i => swap i) swap (\i => Refl) sample

weakeningEvidence :
  rename (liftRenaming Tests.Renaming.collapse) (weaken Tests.Renaming.sample) =
    weaken (rename Tests.Renaming.collapse Tests.Renaming.sample)
weakeningEvidence = renameWeakening collapse sample

public export
checks : List (String, Bool)
checks =
  [ ("renaming identity theorem witness",
      case identityEvidence of
        Refl => sameSyntax (rename Prelude.id sample) sample)
  , ("renaming composition theorem accepts noninjective map",
      case compositionEvidence of
        Refl => sameSyntax (rename FS (rename collapse sample))
                           (rename (FS . collapse) sample))
  , ("renaming congruence needs pointwise equality only",
      case congruenceEvidence of
        Refl => sameSyntax (rename (\i => swap i) sample) (rename swap sample))
  , ("renaming commutes with weakening theorem witness",
      case weakeningEvidence of
        Refl => sameSyntax (rename (liftRenaming collapse) (weaken sample))
                           (weaken (rename collapse sample)))
  ]
