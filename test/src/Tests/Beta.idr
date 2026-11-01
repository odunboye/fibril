module Tests.Beta

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Reduction
import Fibril.Core.Substitution.Instantiation
import Fibril.Core.Reduction.Beta

%default total

-- These samples are scoped raw syntax, not typing derivations.
value : Term 1
value = Apply (Variable FZ) UnitValue

body : Term 2
body = Lambda Linear (Variable FZ)
         (BoolCase BoolTrue (Variable (FS FZ))
           (UnitCase UnitValue (Variable (FS (FS FZ)))))

domain : Term 1
domain = Pi Erased UnitType BoolType

shift : Fin 1 -> Fin 2
shift = FS

replacement : Fin 1 -> Term 2
replacement _ = Lambda Erased BoolType (Variable (FS (FS FZ)))

renameEvidence :
  rename Tests.Beta.shift (instantiateTerm Tests.Beta.value Tests.Beta.body) =
    instantiateTerm (rename Tests.Beta.shift Tests.Beta.value)
                    (rename (liftRenaming Tests.Beta.shift) Tests.Beta.body)
renameEvidence = renameInstantiation shift value body

substituteEvidence :
  substituteTerm Tests.Beta.replacement (instantiateTerm Tests.Beta.value Tests.Beta.body) =
    instantiateTerm (substituteTerm Tests.Beta.replacement Tests.Beta.value)
                    (substituteTerm (liftSubstitution Tests.Beta.replacement) Tests.Beta.body)
substituteEvidence = substituteInstantiation replacement value body

renameStepEvidence :
  step (rename Tests.Beta.shift
    (Apply (Lambda Linear Tests.Beta.domain Tests.Beta.body) Tests.Beta.value)) =
  Just (rename Tests.Beta.shift (instantiateTerm Tests.Beta.value Tests.Beta.body))
renameStepEvidence = renameBetaStep shift Linear domain body value

substituteStepEvidence :
  step (substituteTerm Tests.Beta.replacement
    (Apply (Lambda Erased Tests.Beta.domain Tests.Beta.body) Tests.Beta.value)) =
  Just (substituteTerm Tests.Beta.replacement (instantiateTerm Tests.Beta.value Tests.Beta.body))
substituteStepEvidence = substituteBetaStep replacement Erased domain body value

introduceLambda : Fin 1 -> Term 0
introduceLambda _ = Lambda Erased UnitType BoolTrue

public export
checks : List (String, Bool)
checks =
  [ ("instantiation renaming theorem witness",
      case renameEvidence of
        Refl => sameSyntax (rename shift (instantiateTerm value body))
                           (instantiateTerm (rename shift value) (rename (liftRenaming shift) body)))
  , ("instantiation substitution theorem witness",
      case substituteEvidence of
        Refl => sameSyntax (substituteTerm replacement (instantiateTerm value body))
                           (instantiateTerm (substituteTerm replacement value)
                                            (substituteTerm (liftSubstitution replacement) body)))
  , ("root beta renaming theorem uses actual step",
      case renameStepEvidence of
        Refl => case step (rename shift (Apply (Lambda Linear domain body) value)) of
          Just result => sameSyntax result (rename shift (instantiateTerm value body))
          Nothing => False)
  , ("root beta substitution theorem uses actual step",
      case substituteStepEvidence of
        Refl => case step (substituteTerm replacement (Apply (Lambda Erased domain body) value)) of
          Just result => sameSyntax result (substituteTerm replacement (instantiateTerm value body))
          Nothing => False)
  , ("general step substitution commutation is false: creates redex",
      let neutral : Term 1 = Apply (Variable FZ) UnitValue
       in case (step neutral, step (substituteTerm introduceLambda neutral)) of
         (Nothing, Just result) => sameSyntax result BoolTrue
         _ => False)
  , ("general step substitution commutation is false: changes preferred step",
      let term : Term 1 =
            Apply (Variable FZ) (Apply (Lambda Linear UnitType (Variable FZ)) UnitValue)
       in case (step term, step (substituteTerm introduceLambda term)) of
         (Just before, Just after) =>
           sameSyntax after BoolTrue &&
           not (sameSyntax after (substituteTerm introduceLambda before))
         _ => False)
  ]
