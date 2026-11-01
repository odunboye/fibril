module Tests.SubstitutionComposition

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Substitution.Composition

%default total

-- All constructors, nested binders, and both outer references; no typing claim.
sample : Term 2
sample =
  Pi Erased (Universe 0)
    (Lambda Linear (Variable FZ)
      (BoolCase (Variable (FS (FS FZ)))
        (UnitCase UnitValue (Apply (Variable FZ) BoolTrue))
        (BoolCase BoolFalse (Variable (FS (FS (FS FZ))))
          (Apply (Pi Unrestricted UnitType BoolType)
                 (Lambda Linear StringType (StringValue "data"))))))

first : Fin 2 -> Term 1
first FZ = Apply (Variable FZ) BoolTrue
first (FS FZ) = Lambda Erased UnitType (Variable (FS FZ))

second : Fin 1 -> Term 2
second _ = UnitCase UnitValue (Variable (FS FZ))

collapse : Fin 2 -> Fin 1
collapse _ = FZ

value : Term 2
value = Lambda Linear BoolType
          (BoolCase (Variable FZ) (Variable (FS (FS FZ))) BoolFalse)

renameEvidence :
  rename FS (substituteTerm Tests.SubstitutionComposition.first Tests.SubstitutionComposition.sample) =
    substituteTerm (rename FS . Tests.SubstitutionComposition.first)
                   Tests.SubstitutionComposition.sample
renameEvidence = renameAfterSubstitution FS first sample

substituteEvidence :
  substituteTerm Tests.SubstitutionComposition.second
    (rename Tests.SubstitutionComposition.collapse Tests.SubstitutionComposition.sample) =
  substituteTerm (Tests.SubstitutionComposition.second . Tests.SubstitutionComposition.collapse)
                 Tests.SubstitutionComposition.sample
substituteEvidence = substituteAfterRenaming collapse second sample

weakeningEvidence :
  substituteTerm (liftSubstitution Tests.SubstitutionComposition.first)
                 (weaken Tests.SubstitutionComposition.sample) =
    weaken (substituteTerm Tests.SubstitutionComposition.first Tests.SubstitutionComposition.sample)
weakeningEvidence = substituteWeakening first sample

compositionEvidence :
  substituteTerm Tests.SubstitutionComposition.second
    (substituteTerm Tests.SubstitutionComposition.first Tests.SubstitutionComposition.sample) =
  substituteTerm (substituteTerm Tests.SubstitutionComposition.second . Tests.SubstitutionComposition.first)
                 Tests.SubstitutionComposition.sample
compositionEvidence = substituteComposition first second sample

instantiationEvidence :
  instantiateTerm Tests.SubstitutionComposition.value (weaken Tests.SubstitutionComposition.sample) =
    Tests.SubstitutionComposition.sample
instantiationEvidence = instantiateWeakening value sample

public export
checks : List (String, Bool)
checks =
  [ ("fusion renaming after substitution witness",
      case renameEvidence of
        Refl => sameSyntax (rename FS (substituteTerm first sample))
                           (substituteTerm (rename FS . first) sample))
  , ("fusion substitution after noninjective renaming witness",
      case substituteEvidence of
        Refl => sameSyntax (substituteTerm second (rename collapse sample))
                           (substituteTerm (second . collapse) sample))
  , ("fusion substitution weakening witness",
      case weakeningEvidence of
        Refl => sameSyntax (substituteTerm (liftSubstitution first) (weaken sample))
                           (weaken (substituteTerm first sample)))
  , ("substitution composition theorem changes scopes and lifts replacements",
      case compositionEvidence of
        Refl => sameSyntax (substituteTerm second (substituteTerm first sample))
                           (substituteTerm (substituteTerm second . first) sample))
  , ("instantiation weakening theorem witness",
      case instantiationEvidence of
        Refl => sameSyntax (instantiateTerm value (weaken sample)) sample)
  , ("instantiation shared replacement map",
      sameSyntax (replaceNewest value FZ) value &&
      sameSyntax (replaceNewest value (FS FZ)) (Variable FZ))
  ]
