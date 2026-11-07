module Tests.Quantitative

import Data.Vect
import Fibril.Core.Usage
import Fibril.Core.Quantity
import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Quantitative.Substitution
import Fibril.Core.Quantitative.Usage

%default total

-- These equalities check the actual typed substitution implementation, including
-- open replacements, distinct context types, and lifting through two binders.
captureSafe :
  instantiate (the (Term [BoolTy] BoolTy) (Ref Here))
    (Lam Linear (Lam Linear
      (UnitElim (Ref (There Here))
        (UnitElim (Ref Here) (Ref (There (There Here))))))) =
  Lam Linear (Lam Linear
    (UnitElim (Ref (There Here))
      (UnitElim (Ref Here) (Ref (There (There Here))))))
captureSafe = Refl

boundVariableUnchanged :
  instantiate (the (Term [] BoolTy) (Boolean False))
    (Lam Linear (Ref Here)) = the (Term [] (Arrow Linear UnitTy UnitTy)) (Lam Linear (Ref Here))
boundVariableUnchanged = Refl

tailVariableLowered :
  instantiate (the (Term [UnitTy] BoolTy) (Boolean True))
    (Ref (There Here)) = the (Term [UnitTy] UnitTy) (Ref Here)
tailVariableLowered = Refl

swap : Substitution [BoolTy, UnitTy] [UnitTy, BoolTy]
swap Here = Ref (There Here)
swap (There Here) = Ref Here

simultaneousTyped :
  substitute Tests.Quantitative.swap (If (Ref Here) (Ref (There Here)) Unit) =
  If (Ref (There Here)) (Ref Here) Unit
simultaneousTyped = Refl

functionReplacement :
  instantiate (the (Term [] (Arrow Linear BoolTy BoolTy)) (Lam Linear (Ref Here)))
    (App (Ref Here) (Boolean True)) = App (Lam Linear (Ref Here)) (Boolean True)
functionReplacement = Refl

identity : Term [] (Arrow Linear UnitTy UnitTy)
identity = Lam Linear (Ref Here)

-- A direct quantitative derivation, independent of the inference function.
identityDerivation : Uses Tests.Quantitative.identity []
identityDerivation = UseLam (UseRef Here) Refl

alternative : Term [UnitTy] UnitTy
alternative = If (Boolean True) (UnitElim (Ref Here) Unit) (UnitElim (Ref Here) Unit)

alternativeDerivation : Uses Tests.Quantitative.alternative [Linear]
alternativeDerivation = UseIf UseBoolean (UseUnitElim (UseRef Here) UseUnit)
                                       (UseUnitElim (UseRef Here) UseUnit)

-- The theorem itself, rather than inference alone, checks captures under two
-- binders, an erased application argument, and joined alternatives.
weakeningExample : Term [UnitTy] (Arrow Linear UnitTy (Arrow Linear UnitTy UnitTy))
weakeningExample = Lam Linear (Lam Linear
  (UnitElim (Ref (There Here))
    (UnitElim (Ref Here)
      (If (Boolean True) (Ref (There (There Here)))
        (App (Lam Erased (Ref (There (There (There Here))))) (Ref Here))))))

weakeningExampleUses : Uses Tests.Quantitative.weakeningExample [Linear]
weakeningExampleUses = UseLam (UseLam
  (UseUnitElim (UseRef (There Here))
    (UseUnitElim (UseRef Here)
      (UseIf UseBoolean (UseRef (There (There Here)))
        (UseApp (UseLam (UseRef (There (There (There Here)))) Refl) (UseRef Here))))) Refl) Refl

weakenedExampleUses : Uses (weaken {b=BoolTy} Tests.Quantitative.weakeningExample) [Erased, Linear]
weakenedExampleUses = weakenUses Tests.Quantitative.weakeningExample [Linear] weakeningExampleUses

headCase : (r : Usage 1 ** (Uses (instantiate (the (Term [UnitTy] UnitTy) (Ref Here)) (Ref Here)) r,
                             Admits [Linear] r))
headCase = instantiateHeadUsage (Ref Here) [Linear] [Linear]
  (UseRef Here) (AdmitCons Refl AdmitNil)

alternativeUnique : the (Usage 1) [Linear] = [Linear]
alternativeUnique = usageUnique alternativeDerivation alternativeDerivation

-- The head occurs unrestrictedly in an argument whose overall scale is zero,
-- and once outside it. The hidden occurrence must still have a derivation.
zeroScaledHead : Term [UnitTy, UnitTy] UnitTy
zeroScaledHead = UnitElim
  (App (Lam Erased Unit) (App (Lam Unrestricted Unit) (Ref Here)))
  (Ref Here)

underLinearBinder : Term [UnitTy, UnitTy] (Arrow Linear UnitTy UnitTy)
underLinearBinder = Lam Linear (UnitElim (Ref Here) (Ref (There Here)))

branchCommon : combineUsage (joinUsage [Erased, Linear] [Linear, Linear]) [Linear, Linear] =
               joinUsage (combineUsage [Erased, Linear] [Linear, Linear])
                         (combineUsage [Linear, Linear] [Linear, Linear])
branchCommon = combineJoinCommon [Erased, Linear] [Linear, Linear] [Linear, Linear]

branchParts : (Admits [Unrestricted, Linear] [Erased, Linear],
               Admits [Unrestricted, Linear] [Linear, Linear])
branchParts = admitJoinParts [Unrestricted, Linear] [Erased, Linear] [Linear, Linear]
  (AdmitCons Refl (AdmitCons Refl AdmitNil))

alternativePermission : Admits [Linear] [Linear]
alternativePermission = admitJoin [Linear] [Linear] [Linear]
  (AdmitCons Refl AdmitNil) (AdmitCons Refl AdmitNil)

unused : Term [] (Arrow Linear UnitTy UnitTy)
unused = Lam Linear Unit

duplicated : Term [] (Arrow Linear UnitTy UnitTy)
duplicated = Lam Linear (UnitElim (Ref Here) (Ref Here))

erasedExtraction : Term [] (Arrow Erased BoolTy BoolTy)
erasedExtraction = Lam Erased (Ref Here)

acceptedWith : {n : Nat} -> {0 context : Vect n Ty} -> (permissions, expected : Vect n Quantity) -> Term context a -> Bool
acceptedWith permissions expected term = case checkUsage permissions term of
  Right (actual ** _) => actual == expected
  Left _ => False

rejected : Either UsageError a -> Bool
rejected (Left _) = True
rejected _ = False

binderRejected : Quantity -> Quantity -> Either UsageError a -> Bool
binderRejected expected observed (Left (BinderMismatch p u)) = p == expected && u == observed
binderRejected _ _ _ = False

ambientRejectedAt : Nat -> Either UsageError a -> Bool
ambientRejectedAt expected (Left (AmbientMismatch actual _ _)) = expected == actual
ambientRejectedAt _ _ = False

-- Typed renaming is allowed to contract. This example is deliberately NOT
-- resource safe: two distinct linear resources become one duplicated resource.
contract : Renaming [UnitTy, UnitTy] [UnitTy]
contract Here = Here
contract (There Here) = Here

separateResources : Term [UnitTy, UnitTy] UnitTy
separateResources = UnitElim (Ref Here) (Ref (There Here))

contractReplacements : Substitution [UnitTy, UnitTy] [UnitTy]
contractReplacements variable = Ref (contract variable)

export
checks : List (String, Bool)
checks =
  [ ("common replacement demand distributes through unequal alternative joins", case branchCommon of Refl => True)
  , ("joined permission splits into both exact branch permissions", case branchParts of (AdmitCons _ _, AdmitCons _ _) => True)
  , ("quantitative weakening preserves nested binders, captures and erased arguments", case weakenedExampleUses of UseLam _ _ => True)
  , ("typed substitution weakens an open replacement under two binders", case captureSafe of Refl => True)
  , ("typed head substitution preserves the shadowing binder", case boundVariableUnchanged of Refl => True)
  , ("typed head substitution lowers untouched outer variables", case tailVariableLowered of Refl => True)
  , ("typed simultaneous substitution maps distinct variable types", case simultaneousTyped of Refl => True)
  , ("typed substitution supports function-valued replacements", case functionReplacement of Refl => True)
  , ("quantitative derivation checks linear identity", acceptedWith [] [] Tests.Quantitative.identity)
  , ("quantitative inference rejects unused linear binder", binderRejected Linear Erased (inferUsage unused))
  , ("quantitative inference rejects duplicated linear binder", binderRejected Linear Unrestricted (inferUsage duplicated))
  , ("quantitative inference rejects erased extraction", binderRejected Erased Linear (inferUsage erasedExtraction))
  , ("graded exact substitution formula fails for correlated alternatives",
      acceptedWith [Unrestricted, Unrestricted] [Unrestricted, Unrestricted]
        (the (Term [UnitTy, UnitTy] UnitTy)
          (If (Boolean True) (Ref Here) (Ref (There Here)))) &&
      acceptedWith [Linear] [Linear]
        (instantiate (the (Term [UnitTy] UnitTy) (Ref Here))
          (the (Term [UnitTy, UnitTy] UnitTy)
            (If (Boolean True) (Ref Here) (Ref (There Here))))) &&
      combineUsage [Unrestricted] (scaleUsage Unrestricted [Linear]) == [Unrestricted])
  , ("quantitative alternatives share a linear resource", acceptedWith [Linear] [Linear] alternative)
  , ("quantitative alternatives with differing use need unrestricted permission",
      rejected (checkUsage [Linear] (the (Term [UnitTy] UnitTy) (If (Boolean True) (Ref Here) Unit))) &&
      acceptedWith [Unrestricted] [Unrestricted] (the (Term [UnitTy] UnitTy) (If (Boolean True) (Ref Here) Unit)))
  , ("quantitative condition adds demand to joined branches",
      acceptedWith [Unrestricted] [Unrestricted] (the (Term [BoolTy] BoolTy) (If (Ref Here) (Ref Here) (Ref Here))))
  , ("quantitative lambda retains capture demand",
      acceptedWith [Linear] [Linear]
        (the (Term [BoolTy] (Arrow Linear UnitTy BoolTy))
          (Lam Linear (UnitElim (Ref Here) (Ref (There Here))))))
  , ("quantitative application scales unrestricted argument demand",
      acceptedWith [Unrestricted] [Unrestricted]
        (App (Lam Unrestricted Unit) (the (Term [UnitTy] UnitTy) (Ref Here))))
  , ("quantitative erased application scales demand to zero",
      acceptedWith [Erased] [Erased]
        (App (Lam Erased Unit) (the (Term [BoolTy] BoolTy) (Ref Here))))
  , ("quantitative erased argument still requires internally valid derivation",
      binderRejected Linear Erased (inferUsage
        (the (Term [] UnitTy) (App (Lam Erased Unit) unused))))
  , ("quantitative dead alternative still requires internally valid derivation",
      binderRejected Linear Erased (inferUsage (If (Boolean True) identity unused)))
  , ("quantitative exact permission is not numeric subusage",
      rejected (checkUsage [Linear] (the (Term [BoolTy] UnitTy) Unit)) &&
      rejected (checkUsage [Erased] (the (Term [BoolTy] BoolTy) (Ref Here))))
  , ("typed renaming alone does not preserve linear permissions",
      acceptedWith [Linear, Linear] [Linear, Linear] separateResources &&
      rejected (checkUsage [Linear] (rename contract separateResources)) &&
      acceptedWith [Unrestricted] [Unrestricted] (rename contract separateResources))
  , ("head-reference quantitative lemma returns the replacement demand",
      case headCase of ([Linear] ** _) => True; _ => False)
  , ("exact usage derivations have unique vectors", case alternativeUnique of Refl => True)
  , ("zero-scaled unrestricted head occurrences survive substitution safely in this example",
      acceptedWith [Linear, Erased] [Linear, Erased] zeroScaledHead &&
      acceptedWith [Linear] [Linear] (instantiate (the (Term [UnitTy] UnitTy) (Ref Here)) zeroScaledHead))
  , ("head substitution under a checked linear binder retains its demand",
      acceptedWith [Linear, Erased] [Linear, Erased] underLinearBinder &&
      acceptedWith [Linear] [Linear] (instantiate (the (Term [UnitTy] UnitTy) (Ref Here)) underLinearBinder))
  , ("quantitative head substitution example retains ambient linear permission",
      acceptedWith [Linear] [Linear]
        (instantiate (the (Term [UnitTy] UnitTy) Unit) separateResources))
  , ("quantitative head substitution example combines overlapping captures",
      acceptedWith [Unrestricted] [Unrestricted]
        (instantiate (the (Term [UnitTy] UnitTy) (Ref Here)) separateResources))
  , ("typed simultaneous substitution alone does not preserve linear permissions",
      rejected (checkUsage [Linear] (substitute contractReplacements separateResources)))
  , ("quantitative ambient mismatch reports newest-first variable index",
      ambientRejectedAt 1 (checkUsage [Unrestricted, Linear]
        (the (Term [BoolTy, UnitTy] BoolTy) (Ref Here))))
  , ("typed substitution alone does not enforce internal binder usage",
      binderRejected Linear Erased (inferUsage
        (instantiate (the (Term [] BoolTy) (Boolean True))
          (the (Term [BoolTy] (Arrow Linear UnitTy UnitTy)) unusedBody))))
  ]
  where
    unusedBody : Term [BoolTy] (Arrow Linear UnitTy UnitTy)
    unusedBody = Lam Linear Unit

-- The replacement occurs in both branches, but its linear demand is shared.
alternativeSubstitutionLinear :
  (r : Usage 1 **
    (Uses (instantiate (the (Term [UnitTy] UnitTy) (Ref Here))
      (If (Boolean True) (Ref Here) (Ref Here))) r,
     Admits [Linear] r))
alternativeSubstitutionLinear =
  instantiateAlternativesUsage (Ref Here) True [Linear] [Linear]
    (UseRef Here) (AdmitCons Refl AdmitNil)

alternativeDemandNotSequential :
  joinUsage [Linear] [Linear] = [Linear]
alternativeDemandNotSequential = Refl

alternativeSequentialWouldDuplicate :
  combineUsage [Linear] [Linear] = [Unrestricted]
alternativeSequentialWouldDuplicate = Refl
