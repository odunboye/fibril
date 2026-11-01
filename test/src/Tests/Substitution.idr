module Tests.Substitution

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Substitution

%default total

-- Raw scoped syntax: intentionally no typing or quantity-validity assumption.
sample : Term 1
sample =
  Lambda Linear (Variable FZ)
    (BoolCase BoolTrue (Variable FZ)
      (Apply (Variable (FS FZ)) UnitValue))

replacement : Fin 1 -> Term 1
replacement _ = Apply (Variable FZ) (UnitCase UnitValue BoolTrue)

expected : Term 1
expected =
  Lambda Linear (Apply (Variable FZ) (UnitCase UnitValue BoolTrue))
    (BoolCase BoolTrue (Variable FZ)
      (Apply (Apply (Variable (FS FZ)) (UnitCase UnitValue BoolTrue)) UnitValue))

identityEvidence :
  substituteTerm Variable Tests.Substitution.sample = Tests.Substitution.sample
identityEvidence = substituteIdentity sample

variableEvidence :
  rename FS Tests.Substitution.sample =
    substituteTerm (Variable . FS) Tests.Substitution.sample
variableEvidence = renameAsSubstitution FS sample

congruenceEvidence :
  substituteTerm (\i => Tests.Substitution.replacement i) Tests.Substitution.sample =
    substituteTerm Tests.Substitution.replacement Tests.Substitution.sample
congruenceEvidence =
  substituteCongruent (\i => replacement i) replacement (\i => Refl) sample

-- The annotated domain uses the old scope; replacement in the body is weakened.
captureEvidence :
  substituteTerm Tests.Substitution.replacement Tests.Substitution.sample =
    Tests.Substitution.expected
captureEvidence = Refl

public export
checks : List (String, Bool)
checks =
  [ ("substitution identity theorem witness",
      case identityEvidence of
        Refl => sameSyntax (substituteTerm Variable sample) sample)
  , ("substitution variable correspondence theorem witness",
      case variableEvidence of
        Refl => sameSyntax (rename FS sample) (substituteTerm (Variable . FS) sample))
  , ("substitution pointwise congruence theorem witness",
      case congruenceEvidence of
        Refl => sameSyntax (substituteTerm (\i => replacement i) sample)
                           (substituteTerm replacement sample))
  , ("substitution annotation and capture witness",
      case captureEvidence of
        Refl => sameSyntax (substituteTerm replacement sample) expected)
  ]
