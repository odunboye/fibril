||| A type-preserving ordinary logical fragment. This is a declarative syntax,
||| not the runtime calculus or the abstract-base NeutralExpr checker.
module Fibril.Cubical.Logical.ShadowCommon

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.FaceSoundness
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Cubical.Logical.ShadowSubstitution
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Quantitative.Substitution
import Fibril.Core.Quantitative.Usage
import Fibril.Core.Usage
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.PathContext
import Fibril.Foundation.DeMorgan.Scope

%default total

||| The face solver's independent observations coincide with the pair model's
||| actual endpoint tests when instantiated by a pair valuation.
public export
commonFaceValAgreement : (valuation : Fin d -> DM) -> (face : ScopedFace d) ->
  evalFace (\i, b => valuation i == (b, b)) face = faceAtVal valuation face
commonFaceValAgreement valuation SBottom = Refl
commonFaceValAgreement valuation STop = Refl
commonFaceValAgreement valuation (SEndpoint i b) = Refl
commonFaceValAgreement valuation (SConjunction x y) =
  rewrite commonFaceValAgreement valuation x in rewrite commonFaceValAgreement valuation y in Refl
commonFaceValAgreement valuation (SDisjunction x y) =
  rewrite commonFaceValAgreement valuation x in rewrite commonFaceValAgreement valuation y in Refl

||| An accepted bounded endpoint check really fixes the interval to that endpoint
||| in every satisfying four-pair valuation, including non-Boolean dimensions.
public export
commonBoundedEndpointValSound : {d : Nat} -> (valuation : Fin d -> DM) -> (face : ScopedFace d) ->
  (i : ScopedInterval d) -> (side : Bool) -> boundedEndpointEntails face i side = True ->
  faceAtVal valuation face = True -> evalDMVal valuation i = (side, side)
commonBoundedEndpointValSound valuation face i side accepted holds =
  dmScopedEndpointValSound valuation i side $
    rewrite sym (commonFaceValAgreement valuation (scopedEndpoint i side)) in
    boundedFaceEntailsSound (\j, b => valuation j == (b, b)) face (scopedEndpoint i side)
      (endpointEntailsFace face i side accepted)
      (rewrite commonFaceValAgreement valuation face in holds)

public export
data CommonTerm : Nat -> Type where
  CVar : Fin n -> CommonTerm n
  CUnit : CommonTerm n
  CBool : Bool -> CommonTerm n
  CLam : CommonTerm (S n) -> CommonTerm n
  CApp : CommonTerm n -> CommonTerm n -> CommonTerm n
  CUnitElim : CommonTerm n -> CommonTerm n -> CommonTerm n
  CIf : CommonTerm n -> CommonTerm n -> CommonTerm n -> CommonTerm n

||| Renaming and substitution act directly on common syntax, independently of
||| logical terms. The lifted environment keeps the binder at index zero.
public export
liftCommonRenaming : (Fin n -> Fin m) -> Fin (S n) -> Fin (S m)
liftCommonRenaming rho FZ = FZ
liftCommonRenaming rho (FS i) = FS (rho i)

public export
renameCommon : (Fin n -> Fin m) -> CommonTerm n -> CommonTerm m
renameCommon rho (CVar i) = CVar (rho i)
renameCommon rho CUnit = CUnit
renameCommon rho (CBool b) = CBool b
renameCommon rho (CLam b) = CLam (renameCommon (liftCommonRenaming rho) b)
renameCommon rho (CApp f x) = CApp (renameCommon rho f) (renameCommon rho x)
renameCommon rho (CUnitElim x b) = CUnitElim (renameCommon rho x) (renameCommon rho b)
renameCommon rho (CIf c t f) = CIf (renameCommon rho c) (renameCommon rho t) (renameCommon rho f)

public export
liftCommonSubstitution : (Fin n -> CommonTerm m) -> Fin (S n) -> CommonTerm (S m)
liftCommonSubstitution sigma FZ = CVar FZ
liftCommonSubstitution sigma (FS i) = renameCommon FS (sigma i)

public export
substituteCommon : (Fin n -> CommonTerm m) -> CommonTerm n -> CommonTerm m
substituteCommon sigma (CVar i) = sigma i
substituteCommon sigma CUnit = CUnit
substituteCommon sigma (CBool b) = CBool b
substituteCommon sigma (CLam b) = CLam (substituteCommon (liftCommonSubstitution sigma) b)
substituteCommon sigma (CApp f x) = CApp (substituteCommon sigma f) (substituteCommon sigma x)
substituteCommon sigma (CUnitElim x b) = CUnitElim (substituteCommon sigma x) (substituteCommon sigma b)
substituteCommon sigma (CIf c t f) = CIf (substituteCommon sigma c) (substituteCommon sigma t) (substituteCommon sigma f)

public export
data CommonHasType : (0 ctx : Vect n LogicalType) -> CommonTerm n -> (0 ty : LogicalType) -> Type where
  CVariable : (v : LogicalVar ctx a) -> CommonHasType ctx (CVar (variableIndex v)) a
  CUnitType : CommonHasType ctx CUnit LUnit
  CBoolType : CommonHasType ctx (CBool b) LBool
  CLambdaType : CommonHasType (a :: ctx) body b -> CommonHasType ctx (CLam body) (LArrow a b)
  CApplicationType : CommonHasType ctx f (LArrow a b) -> CommonHasType ctx x a -> CommonHasType ctx (CApp f x) b
  CUnitEliminationType : CommonHasType ctx x LUnit -> CommonHasType ctx body a -> CommonHasType ctx (CUnitElim x body) a
  CConditionalType : CommonHasType ctx c LBool -> CommonHasType ctx t a -> CommonHasType ctx f a -> CommonHasType ctx (CIf c t f) a

||| An indexed environment preserves the type of each actual variable.
public export
CommonRenamingTyped : {0 n, m : Nat} -> (0 source : Vect n LogicalType) -> (0 target : Vect m LogicalType) -> (Fin n -> Fin m) -> Type
CommonRenamingTyped source target rho = {0 a : LogicalType} -> (v : LogicalVar source a) -> (w : LogicalVar target a ** variableIndex w = rho (variableIndex v))

||| Every scoped index has a variable witness at its Vect lookup type.
public export
commonVarAt : (ctx : Vect n LogicalType) -> (i : Fin n) -> LogicalVar ctx (index i ctx)
commonVarAt (a :: ctx) FZ = LHere
commonVarAt (a :: ctx) (FS i) = LThere (commonVarAt ctx i)

public export
commonVarAtIndex : (ctx : Vect n LogicalType) -> (i : Fin n) -> variableIndex (commonVarAt ctx i) = i
commonVarAtIndex (a :: ctx) FZ = Refl
commonVarAtIndex (a :: ctx) (FS i) = cong FS (commonVarAtIndex ctx i)

public export
commonVarLookup : (v : LogicalVar ctx a) -> index (variableIndex v) ctx = a
commonVarLookup LHere = Refl
commonVarLookup (LThere v) = commonVarLookup v

public export
liftCommonRenamingTyped : CommonRenamingTyped source target rho -> CommonRenamingTyped (binder :: source) (binder :: target) (liftCommonRenaming rho)
liftCommonRenamingTyped env LHere = (LHere ** Refl)
liftCommonRenamingTyped env (LThere v) = let (w ** eq) = env v in (LThere w ** cong FS eq)

public export
renameCommonTyped : {0 source : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  (rho : Fin n -> Fin m) -> CommonRenamingTyped source target rho ->
  CommonHasType source t a -> CommonHasType target (renameCommon rho t) a
renameCommonTyped rho env (CVariable v) = let (w ** eq) = env v in rewrite sym eq in CVariable w
renameCommonTyped rho env CUnitType = CUnitType
renameCommonTyped rho env CBoolType = CBoolType
renameCommonTyped rho env (CLambdaType b) = CLambdaType (renameCommonTyped (liftCommonRenaming rho) (liftCommonRenamingTyped env) b)
renameCommonTyped rho env (CApplicationType f x) = CApplicationType (renameCommonTyped rho env f) (renameCommonTyped rho env x)
renameCommonTyped rho env (CUnitEliminationType x b) = CUnitEliminationType (renameCommonTyped rho env x) (renameCommonTyped rho env b)
renameCommonTyped rho env (CConditionalType c t f) = CConditionalType (renameCommonTyped rho env c) (renameCommonTyped rho env t) (renameCommonTyped rho env f)

||| Each image has the type of the variable at its exact index.
public export
CommonSubstitutionTyped : {0 n, m : Nat} -> (0 source : Vect n LogicalType) -> (0 target : Vect m LogicalType) -> (Fin n -> CommonTerm m) -> Type
CommonSubstitutionTyped source target sigma = {0 a : LogicalType} -> (v : LogicalVar source a) -> CommonHasType target (sigma (variableIndex v)) a

public export
liftCommonSubstitutionTyped : {0 source : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  (sigma : Fin n -> CommonTerm m) -> CommonSubstitutionTyped source target sigma ->
  CommonSubstitutionTyped (binder :: source) (binder :: target) (liftCommonSubstitution sigma)
liftCommonSubstitutionTyped sigma env LHere = CVariable LHere
liftCommonSubstitutionTyped sigma env (LThere v) = renameCommonTyped FS (\w => (LThere w ** Refl)) (env v)

public export
substituteCommonTyped : {0 source : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  (sigma : Fin n -> CommonTerm m) -> CommonSubstitutionTyped source target sigma ->
  CommonHasType source t a -> CommonHasType target (substituteCommon sigma t) a
substituteCommonTyped sigma env (CVariable v) = env v
substituteCommonTyped sigma env CUnitType = CUnitType
substituteCommonTyped sigma env CBoolType = CBoolType
substituteCommonTyped sigma env (CLambdaType b) = CLambdaType (substituteCommonTyped (liftCommonSubstitution sigma) (liftCommonSubstitutionTyped sigma env) b)
substituteCommonTyped sigma env (CApplicationType f x) = CApplicationType (substituteCommonTyped sigma env f) (substituteCommonTyped sigma env x)
substituteCommonTyped sigma env (CUnitEliminationType x b) = CUnitEliminationType (substituteCommonTyped sigma env x) (substituteCommonTyped sigma env b)
substituteCommonTyped sigma env (CConditionalType c t f) = CConditionalType (substituteCommonTyped sigma env c) (substituteCommonTyped sigma env t) (substituteCommonTyped sigma env f)

public export
commonTerm : {0 ctx : Vect n LogicalType} -> LogicalTerm ctx a -> CommonTerm n
commonTerm (LRef v) = CVar (variableIndex v)
commonTerm LUnitValue = CUnit
commonTerm (LBoolean b) = CBool b
commonTerm (LLam body) = CLam (commonTerm body)
commonTerm (LApp f x) = CApp (commonTerm f) (commonTerm x)
commonTerm (LUnitElim x body) = CUnitElim (commonTerm x) (commonTerm body)
commonTerm (LIf c t f) = CIf (commonTerm c) (commonTerm t) (commonTerm f)

public export
commonTermTyped : (t : LogicalTerm ctx a) -> CommonHasType ctx (commonTerm t) a
commonTermTyped (LRef v) = CVariable v
commonTermTyped LUnitValue = CUnitType
commonTermTyped (LBoolean b) = CBoolType
commonTermTyped (LLam body) = CLambdaType (commonTermTyped body)
commonTermTyped (LApp f x) = CApplicationType (commonTermTyped f) (commonTermTyped x)
commonTermTyped (LUnitElim x body) = CUnitEliminationType (commonTermTyped x) (commonTermTyped body)
commonTermTyped (LIf c t f) = CConditionalType (commonTermTyped c) (commonTermTyped t) (commonTermTyped f)

||| Pointwise agreement avoids equality of renaming functions.
public export
CommonRenamingRelation : {0 source : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  LogicalRenaming source target -> (Fin n -> Fin m) -> Type
CommonRenamingRelation rho env = {0 a : LogicalType} -> (v : LogicalVar source a) ->
  variableIndex (rho v) = env (variableIndex v)

public export
liftCommonRenamingRelation : (rho : LogicalRenaming source target) -> (env : Fin n -> Fin m) ->
  CommonRenamingRelation rho env -> CommonRenamingRelation (liftLogicalRenaming {a = binder} rho) (liftCommonRenaming env)
liftCommonRenamingRelation rho env rel LHere = Refl
liftCommonRenamingRelation rho env rel (LThere v) = cong FS (rel v)

public export
commonRenameCommutes : (rho : LogicalRenaming source target) -> (env : Fin n -> Fin m) ->
  CommonRenamingRelation rho env -> (t : LogicalTerm source a) ->
  commonTerm (renameLogical rho t) = renameCommon env (commonTerm t)
commonRenameCommutes rho env rel (LRef v) = cong CVar (rel v)
commonRenameCommutes rho env rel LUnitValue = Refl
commonRenameCommutes rho env rel (LBoolean b) = Refl
commonRenameCommutes rho env rel (LLam b) = cong CLam (commonRenameCommutes (liftLogicalRenaming rho) (liftCommonRenaming env) (liftCommonRenamingRelation rho env rel) b)
commonRenameCommutes rho env rel (LApp f x) = cong2 CApp (commonRenameCommutes rho env rel f) (commonRenameCommutes rho env rel x)
commonRenameCommutes rho env rel (LUnitElim x b) = cong2 CUnitElim (commonRenameCommutes rho env rel x) (commonRenameCommutes rho env rel b)
commonRenameCommutes rho env rel (LIf c t f) = rewrite commonRenameCommutes rho env rel c in rewrite commonRenameCommutes rho env rel t in rewrite commonRenameCommutes rho env rel f in Refl

||| Agreement is indexed by the type of each logical variable.
public export
CommonSubstitutionRelation : {0 source : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  LogicalSubstitution source target -> (Fin n -> CommonTerm m) -> Type
CommonSubstitutionRelation sigma env = {0 a : LogicalType} -> (v : LogicalVar source a) ->
  commonTerm (sigma v) = env (variableIndex v)

public export
liftCommonSubstitutionRelation : (sigma : LogicalSubstitution source target) -> (env : Fin n -> CommonTerm m) ->
  CommonSubstitutionRelation sigma env -> CommonSubstitutionRelation (liftLogicalSubstitution {a = binder} sigma) (liftCommonSubstitution env)
liftCommonSubstitutionRelation sigma env rel LHere = Refl
liftCommonSubstitutionRelation sigma env rel (LThere v) =
  trans (commonRenameCommutes LThere FS (\w => Refl) (sigma v)) (cong (renameCommon FS) (rel v))

public export
commonSubstitutionCommutes : (sigma : LogicalSubstitution source target) -> (env : Fin n -> CommonTerm m) ->
  CommonSubstitutionRelation sigma env -> (t : LogicalTerm source a) ->
  commonTerm (substituteLogical sigma t) = substituteCommon env (commonTerm t)
commonSubstitutionCommutes sigma env rel (LRef v) = rel v
commonSubstitutionCommutes sigma env rel LUnitValue = Refl
commonSubstitutionCommutes sigma env rel (LBoolean b) = Refl
commonSubstitutionCommutes sigma env rel (LLam b) = cong CLam (commonSubstitutionCommutes (liftLogicalSubstitution sigma) (liftCommonSubstitution env) (liftCommonSubstitutionRelation sigma env rel) b)
commonSubstitutionCommutes sigma env rel (LApp f x) = cong2 CApp (commonSubstitutionCommutes sigma env rel f) (commonSubstitutionCommutes sigma env rel x)
commonSubstitutionCommutes sigma env rel (LUnitElim x b) = cong2 CUnitElim (commonSubstitutionCommutes sigma env rel x) (commonSubstitutionCommutes sigma env rel b)
commonSubstitutionCommutes sigma env rel (LIf c t f) = rewrite commonSubstitutionCommutes sigma env rel c in rewrite commonSubstitutionCommutes sigma env rel t in rewrite commonSubstitutionCommutes sigma env rel f in Refl

||| The canonical independent environment reads the typed logical image at each index.
public export
commonImageSubstitution : {0 target : Vect m LogicalType} -> (source : Vect n LogicalType) -> LogicalSubstitution source target -> Fin n -> CommonTerm m
commonImageSubstitution source sigma i = commonTerm (sigma (commonVarAt source i))

public export
commonImageSubstitutionCorrect : (source : Vect n LogicalType) -> (sigma : LogicalSubstitution source target) ->
  CommonSubstitutionRelation sigma (commonImageSubstitution source sigma)
commonImageSubstitutionCorrect (a :: source) sigma LHere = Refl
commonImageSubstitutionCorrect (a :: source) sigma (LThere v) =
  commonImageSubstitutionCorrect source (\w => sigma (LThere w)) v

public export
commonImageSubstitutionTyped : (source : Vect n LogicalType) -> (sigma : LogicalSubstitution source target) ->
  CommonSubstitutionTyped source target (commonImageSubstitution source sigma)
commonImageSubstitutionTyped source sigma v =
  rewrite sym (commonImageSubstitutionCorrect source sigma v) in commonTermTyped (sigma v)

||| The ordinary source translation retains its actual shadow type and context.
public export
sourceCommonTyped : (t : Term ctx a) -> CommonHasType (shadowContext ctx) (commonTerm (shadowTerm t)) (shadowType a)
sourceCommonTyped t = commonTermTyped (shadowTerm t)

||| Existing source substitution commutation also holds after common erasure.
public export
sourceCommonSubstitution : (ctx : Vect n Ty) -> (sigma : Substitution ctx target) -> (t : Term ctx a) ->
  commonTerm (shadowTerm (substitute sigma t)) =
  commonTerm (substituteLogical (imageSubstitution ctx sigma) (shadowTerm t))
sourceCommonSubstitution ctx sigma t = cong commonTerm (shadowSubstitutionCommutes ctx sigma t)

||| Source substitution commutes with the independent common environment.
public export
sourceIndependentCommonSubstitution : (source : Vect n Ty) -> {0 target : Vect m Ty} ->
  (sigma : Substitution source target) -> (t : Term source a) ->
  commonTerm (shadowTerm (substitute sigma t)) =
  substituteCommon (commonImageSubstitution (shadowContext source) (imageSubstitution source sigma)) (commonTerm (shadowTerm t))
sourceIndependentCommonSubstitution source sigma t =
  trans (cong commonTerm (shadowSubstitutionCommutes source sigma t))
    (commonSubstitutionCommutes (imageSubstitution source sigma)
      (commonImageSubstitution (shadowContext source) (imageSubstitution source sigma))
      (commonImageSubstitutionCorrect (shadowContext source) (imageSubstitution source sigma)) (shadowTerm t))

public export
sourceIndependentCommonQuantitative : {n : Nat} -> (source : Vect (S n) Ty) -> {0 target : Vect n Ty} ->
  (s : SingleSubstitution source target) -> (term : Term source a) ->
  (usage : Usage (S n)) -> Uses term usage ->
  (replacement : Usage n) -> ReplacementUses s replacement ->
  (SubstitutionResult s term usage replacement,
   commonTerm (shadowTerm (substitute (singleSubstitution s) term)) =
   substituteCommon (commonImageSubstitution (shadowContext source) (imageSubstitution source (singleSubstitution s))) (commonTerm (shadowTerm term)))
sourceIndependentCommonQuantitative source s term usage used replacement replacementUsed =
  (substituteUses s term usage used replacement replacementUsed,
   sourceIndependentCommonSubstitution source (singleSubstitution s) term)

||| The overlap with the existing target is only the abstract-base variable
||| fragment. This erasure intentionally does not claim preservation of Bool.
public export
commonVariableErasure : (v : LogicalVar ctx a) -> (paths : PathContext n k) -> (face : ScopedFace d) ->
  NeutralHasType paths face (NBase (variableIndex v)) NType
commonVariableErasure v paths face = NBaseVar (variableIndex v)

||| Dimension-scoped common syntax. Embedded ordinary terms retain their own
||| de Bruijn context; path names use a separate context.
public export
data CommonPathTerm : Nat -> Nat -> Nat -> Type where
  CPOrdinary : CommonTerm n -> CommonPathTerm n k d
  CPAt : Fin k -> ScopedInterval d -> CommonPathTerm n k d
  CPLam : CommonPathTerm (S n) k d -> CommonPathTerm n k d
  CPApp : CommonPathTerm n k d -> CommonPathTerm n k d -> CommonPathTerm n k d
  CPUnitElim : CommonPathTerm n k d -> CommonPathTerm n k d -> CommonPathTerm n k d
  CPIf : CommonPathTerm n k d -> CommonPathTerm n k d -> CommonPathTerm n k d -> CommonPathTerm n k d

||| Ordinary substitution does not change named paths or dimensions.
public export
substituteCommonPath : (Fin n -> CommonTerm m) -> CommonPathTerm n k d -> CommonPathTerm m k d
substituteCommonPath sigma (CPOrdinary t) = CPOrdinary (substituteCommon sigma t)
substituteCommonPath sigma (CPAt p i) = CPAt p i
substituteCommonPath sigma (CPLam b) = CPLam (substituteCommonPath (liftCommonSubstitution sigma) b)
substituteCommonPath sigma (CPApp f x) = CPApp (substituteCommonPath sigma f) (substituteCommonPath sigma x)
substituteCommonPath sigma (CPUnitElim x b) = CPUnitElim (substituteCommonPath sigma x) (substituteCommonPath sigma b)
substituteCommonPath sigma (CPIf c t f) = CPIf (substituteCommonPath sigma c) (substituteCommonPath sigma t) (substituteCommonPath sigma f)

public export
data CommonPathHasType : (0 ctx : Vect n LogicalType) -> (0 paths : Vect k LogicalType) -> CommonPathTerm n k d -> (0 ty : LogicalType) -> Type where
  CPOrdinaryType : CommonHasType ctx t a -> CommonPathHasType ctx paths (CPOrdinary t) a
  CPAtType : (p : LogicalVar paths a) -> CommonPathHasType ctx paths (CPAt (variableIndex p) i) a
  CPLamType : CommonPathHasType (a :: ctx) paths b c -> CommonPathHasType ctx paths (CPLam b) (LArrow a c)
  CPAppType : CommonPathHasType ctx paths f (LArrow a b) -> CommonPathHasType ctx paths x a -> CommonPathHasType ctx paths (CPApp f x) b
  CPUnitElimType : CommonPathHasType ctx paths x LUnit -> CommonPathHasType ctx paths b a -> CommonPathHasType ctx paths (CPUnitElim x b) a
  CPIfType : CommonPathHasType ctx paths c LBool -> CommonPathHasType ctx paths t a -> CommonPathHasType ctx paths f a -> CommonPathHasType ctx paths (CPIf c t f) a

public export
renameCommonPath : (Fin n -> Fin m) -> CommonPathTerm n k d -> CommonPathTerm m k d
renameCommonPath rho (CPOrdinary t) = CPOrdinary (renameCommon rho t)
renameCommonPath rho (CPAt p i) = CPAt p i
renameCommonPath rho (CPLam b) = CPLam (renameCommonPath (liftCommonRenaming rho) b)
renameCommonPath rho (CPApp f x) = CPApp (renameCommonPath rho f) (renameCommonPath rho x)
renameCommonPath rho (CPUnitElim x b) = CPUnitElim (renameCommonPath rho x) (renameCommonPath rho b)
renameCommonPath rho (CPIf c t f) = CPIf (renameCommonPath rho c) (renameCommonPath rho t) (renameCommonPath rho f)

public export
renameCommonPathTyped : {0 source : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  (rho : Fin n -> Fin m) -> CommonRenamingTyped source target rho ->
  CommonPathHasType source paths t a -> CommonPathHasType target paths (renameCommonPath rho t) a
renameCommonPathTyped rho env (CPOrdinaryType t) = CPOrdinaryType (renameCommonTyped rho env t)
renameCommonPathTyped rho env (CPAtType p) = CPAtType p
renameCommonPathTyped rho env (CPLamType b) = CPLamType (renameCommonPathTyped (liftCommonRenaming rho) (liftCommonRenamingTyped env) b)
renameCommonPathTyped rho env (CPAppType f x) = CPAppType (renameCommonPathTyped rho env f) (renameCommonPathTyped rho env x)
renameCommonPathTyped rho env (CPUnitElimType x b) = CPUnitElimType (renameCommonPathTyped rho env x) (renameCommonPathTyped rho env b)
renameCommonPathTyped rho env (CPIfType c t f) = CPIfType (renameCommonPathTyped rho env c) (renameCommonPathTyped rho env t) (renameCommonPathTyped rho env f)

public export
substituteCommonPathTyped : {0 source : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  (sigma : Fin n -> CommonTerm m) -> CommonSubstitutionTyped source target sigma ->
  CommonPathHasType source paths t a -> CommonPathHasType target paths (substituteCommonPath sigma t) a
substituteCommonPathTyped sigma env (CPOrdinaryType t) = CPOrdinaryType (substituteCommonTyped sigma env t)
substituteCommonPathTyped sigma env (CPAtType p) = CPAtType p
substituteCommonPathTyped sigma env (CPLamType b) = CPLamType (substituteCommonPathTyped (liftCommonSubstitution sigma) (liftCommonSubstitutionTyped sigma env) b)
substituteCommonPathTyped sigma env (CPAppType f x) = CPAppType (substituteCommonPathTyped sigma env f) (substituteCommonPathTyped sigma env x)
substituteCommonPathTyped sigma env (CPUnitElimType x b) = CPUnitElimType (substituteCommonPathTyped sigma env x) (substituteCommonPathTyped sigma env b)
substituteCommonPathTyped sigma env (CPIfType c t f) = CPIfType (substituteCommonPathTyped sigma env c) (substituteCommonPathTyped sigma env t) (substituteCommonPathTyped sigma env f)

public export
commonPathTerm : {0 context : Vect n LogicalType} -> {0 paths : Vect k LogicalType} ->
  PathBody context paths d a -> CommonPathTerm n k d
commonPathTerm (Embed t) = CPOrdinary (commonTerm t)
commonPathTerm (NeutralAt p i) = CPAt (variableIndex p) i
commonPathTerm (BodyLam b) = CPLam (commonPathTerm b)
commonPathTerm (BodyApp f x) = CPApp (commonPathTerm f) (commonPathTerm x)
commonPathTerm (BodyUnitElim x b) = CPUnitElim (commonPathTerm x) (commonPathTerm b)
commonPathTerm (BodyIf c t f) = CPIf (commonPathTerm c) (commonPathTerm t) (commonPathTerm f)

public export
commonPathSubstitutionCommutes : (sigma : LogicalSubstitution context target) -> (env : Fin n -> CommonTerm m) ->
  CommonSubstitutionRelation sigma env -> (body : PathBody context paths d a) ->
  commonPathTerm (mapPathTerms sigma body) = substituteCommonPath env (commonPathTerm body)
commonPathSubstitutionCommutes sigma env rel (Embed t) = cong CPOrdinary (commonSubstitutionCommutes sigma env rel t)
commonPathSubstitutionCommutes sigma env rel (NeutralAt p i) = Refl
commonPathSubstitutionCommutes sigma env rel (BodyLam b) = cong CPLam (commonPathSubstitutionCommutes (liftLogicalSubstitution sigma) (liftCommonSubstitution env) (liftCommonSubstitutionRelation sigma env rel) b)
commonPathSubstitutionCommutes sigma env rel (BodyApp f x) = cong2 CPApp (commonPathSubstitutionCommutes sigma env rel f) (commonPathSubstitutionCommutes sigma env rel x)
commonPathSubstitutionCommutes sigma env rel (BodyUnitElim x b) = cong2 CPUnitElim (commonPathSubstitutionCommutes sigma env rel x) (commonPathSubstitutionCommutes sigma env rel b)
commonPathSubstitutionCommutes sigma env rel (BodyIf c t f) = rewrite commonPathSubstitutionCommutes sigma env rel c in rewrite commonPathSubstitutionCommutes sigma env rel t in rewrite commonPathSubstitutionCommutes sigma env rel f in Refl

public export
commonPathTermTyped : (body : PathBody context paths d a) ->
  CommonPathHasType context paths (commonPathTerm body) a
commonPathTermTyped (Embed t) = CPOrdinaryType (commonTermTyped t)
commonPathTermTyped (NeutralAt p i) = CPAtType p
commonPathTermTyped (BodyLam b) = CPLamType (commonPathTermTyped b)
commonPathTermTyped (BodyApp f x) = CPAppType (commonPathTermTyped f) (commonPathTermTyped x)
commonPathTermTyped (BodyUnitElim x b) = CPUnitElimType (commonPathTermTyped x) (commonPathTermTyped b)
commonPathTermTyped (BodyIf c t f) = CPIfType (commonPathTermTyped c) (commonPathTermTyped t) (commonPathTermTyped f)

||| Dimension substitution leaves ordinary terms and term binders unchanged.
public export
mapCommonPathDimensions : (Fin d -> ScopedInterval e) -> CommonPathTerm n k d -> CommonPathTerm n k e
mapCommonPathDimensions env (CPOrdinary t) = CPOrdinary t
mapCommonPathDimensions env (CPAt p i) = CPAt p (substituteScoped env i)
mapCommonPathDimensions env (CPLam b) = CPLam (mapCommonPathDimensions env b)
mapCommonPathDimensions env (CPApp f x) = CPApp (mapCommonPathDimensions env f) (mapCommonPathDimensions env x)
mapCommonPathDimensions env (CPUnitElim x b) = CPUnitElim (mapCommonPathDimensions env x) (mapCommonPathDimensions env b)
mapCommonPathDimensions env (CPIf c t f) = CPIf (mapCommonPathDimensions env c) (mapCommonPathDimensions env t) (mapCommonPathDimensions env f)

||| The two operations affect disjoint scopes, including under binders.
public export
commonPathMixedSubstitution : (sigma : Fin n -> CommonTerm m) ->
  (dims : Fin d -> ScopedInterval e) -> (body : CommonPathTerm n k d) ->
  mapCommonPathDimensions dims (substituteCommonPath sigma body) =
  substituteCommonPath sigma (mapCommonPathDimensions dims body)
commonPathMixedSubstitution sigma dims (CPOrdinary t) = Refl
commonPathMixedSubstitution sigma dims (CPAt p i) = Refl
commonPathMixedSubstitution sigma dims (CPLam b) = cong CPLam (commonPathMixedSubstitution (liftCommonSubstitution sigma) dims b)
commonPathMixedSubstitution sigma dims (CPApp f x) = cong2 CPApp (commonPathMixedSubstitution sigma dims f) (commonPathMixedSubstitution sigma dims x)
commonPathMixedSubstitution sigma dims (CPUnitElim x b) = cong2 CPUnitElim (commonPathMixedSubstitution sigma dims x) (commonPathMixedSubstitution sigma dims b)
commonPathMixedSubstitution sigma dims (CPIf c t f) = rewrite commonPathMixedSubstitution sigma dims c in rewrite commonPathMixedSubstitution sigma dims t in rewrite commonPathMixedSubstitution sigma dims f in Refl

public export
commonPathDimensionsCommute : (env : Fin d -> ScopedInterval e) -> (body : PathBody context paths d a) ->
  commonPathTerm (mapPathDimensions env body) = mapCommonPathDimensions env (commonPathTerm body)
commonPathDimensionsCommute env (Embed t) = Refl
commonPathDimensionsCommute env (NeutralAt p i) = Refl
commonPathDimensionsCommute env (BodyLam b) = cong CPLam (commonPathDimensionsCommute env b)
commonPathDimensionsCommute env (BodyApp f x) = cong2 CPApp (commonPathDimensionsCommute env f) (commonPathDimensionsCommute env x)
commonPathDimensionsCommute env (BodyUnitElim x b) = cong2 CPUnitElim (commonPathDimensionsCommute env x) (commonPathDimensionsCommute env b)
commonPathDimensionsCommute env (BodyIf c t f) = rewrite commonPathDimensionsCommute env c in rewrite commonPathDimensionsCommute env t in rewrite commonPathDimensionsCommute env f in Refl

||| Dimension-independent, intrinsically typed common path declarations.
public export
data CommonDeclarations : Vect n LogicalType -> Vect k LogicalType -> Type where
  CommonNoPaths : CommonDeclarations ctx []
  CommonDeclarePath : (left, right : CommonTerm n) ->
    (0 leftType : CommonHasType ctx left a) -> (0 rightType : CommonHasType ctx right a) ->
    CommonDeclarations ctx paths -> CommonDeclarations ctx (a :: paths)

||| Substitute every actual endpoint with the same typed environment.
public export
substituteCommonDeclarations : {0 source : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  (sigma : Fin n -> CommonTerm m) -> CommonSubstitutionTyped source target sigma ->
  CommonDeclarations source paths -> CommonDeclarations target paths
substituteCommonDeclarations sigma env CommonNoPaths = CommonNoPaths
substituteCommonDeclarations sigma env (CommonDeclarePath l r lt rt rest) =
  CommonDeclarePath (substituteCommon sigma l) (substituteCommon sigma r)
    (substituteCommonTyped sigma env lt) (substituteCommonTyped sigma env rt)
    (substituteCommonDeclarations sigma env rest)

public export
commonDeclarations : (decls : PathDeclarations ctx paths) -> CommonDeclarations ctx paths
commonDeclarations NoPaths = CommonNoPaths
commonDeclarations (DeclarePath l r rest) =
  CommonDeclarePath (commonTerm l) (commonTerm r) (commonTermTyped l) (commonTermTyped r) (commonDeclarations rest)

public export
data CommonDeclaredPath : {0 ctx : Vect n LogicalType} -> {0 paths : Vect k LogicalType} -> CommonDeclarations ctx paths -> LogicalVar paths a -> CommonTerm n -> CommonTerm n -> Type where
  CommonDeclaredHere : CommonDeclaredPath (CommonDeclarePath l r lt rt rest) LHere l r
  CommonDeclaredThere : CommonDeclaredPath rest p l r ->
    CommonDeclaredPath (CommonDeclarePath x y xt yt rest) (LThere p) l r

public export
substituteCommonDeclaredPath : {0 source : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  (sigma : Fin n -> CommonTerm m) -> (env : CommonSubstitutionTyped source target sigma) ->
  (decls : CommonDeclarations source paths) ->
  CommonDeclaredPath decls p l r ->
  CommonDeclaredPath (substituteCommonDeclarations sigma env decls) p (substituteCommon sigma l) (substituteCommon sigma r)
substituteCommonDeclaredPath sigma env (CommonDeclarePath l r lt rt rest) CommonDeclaredHere = CommonDeclaredHere
substituteCommonDeclaredPath sigma env (CommonDeclarePath x y xt yt rest) (CommonDeclaredThere p) =
  CommonDeclaredThere (substituteCommonDeclaredPath sigma env rest p)

public export
commonDeclaredPath : {0 decls : PathDeclarations ctx paths} ->
  {0 p : LogicalVar paths a} -> {0 l, r : LogicalTerm ctx a} ->
  DeclaredPath decls p l r -> CommonDeclaredPath (commonDeclarations decls) p (commonTerm l) (commonTerm r)
commonDeclaredPath DeclaredHere = CommonDeclaredHere
commonDeclaredPath (DeclaredThere p) = CommonDeclaredThere (commonDeclaredPath p)

||| Equality under the exact face; constructors carry independent typing evidence.
public export
data CommonFaceEqual : {0 ctx : Vect n LogicalType} -> {0 paths : Vect k LogicalType} -> CommonDeclarations ctx paths -> ScopedFace d ->
  CommonPathTerm n k d -> CommonPathTerm n k d -> (0 ty : LogicalType) -> Type where
  CommonRefl : {0 ctx : Vect n LogicalType} -> {0 paths : Vect k LogicalType} -> {0 decls : CommonDeclarations ctx paths} -> (0 typed : CommonPathHasType ctx paths x a) -> CommonFaceEqual decls face x x a
  CommonSym : CommonFaceEqual decls face x y a -> CommonFaceEqual decls face y x a
  CommonTrans : CommonFaceEqual decls face x y a -> CommonFaceEqual decls face y z a -> CommonFaceEqual decls face x z a
  CommonLeft : CommonDeclaredPath decls p l r -> boundedEndpointEntails face i False = True ->
    CommonFaceEqual decls face (CPAt (variableIndex p) i) (CPOrdinary l) a
  CommonRight : CommonDeclaredPath decls p l r -> boundedEndpointEntails face i True = True ->
    CommonFaceEqual decls face (CPAt (variableIndex p) i) (CPOrdinary r) a
  CommonRestrict : {0 ctx : Vect n LogicalType} -> {0 paths : Vect k LogicalType} -> {0 decls : CommonDeclarations ctx paths} -> {0 face : ScopedFace d} -> {0 x, y : CommonPathTerm n k d} -> {source : ScopedFace d} -> CommonFaceEqual decls source x y a ->
    boundedFaceEntails face source = True -> CommonFaceEqual decls face x y a
  CommonAppEqual : CommonFaceEqual decls face f g (LArrow a b) -> CommonFaceEqual decls face x y a ->
    CommonFaceEqual decls face (CPApp f x) (CPApp g y) b
  CommonIfEqual : CommonFaceEqual decls face c c' LBool -> CommonFaceEqual decls face t t' a ->
    CommonFaceEqual decls face f f' a -> CommonFaceEqual decls face (CPIf c t f) (CPIf c' t' f') a
  CommonUnitElimEqual : CommonFaceEqual decls face x y LUnit -> CommonFaceEqual decls face b b' a ->
    CommonFaceEqual decls face (CPUnitElim x b) (CPUnitElim y b') a

public export
substituteCommonFaceEqual : {0 source : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  (sigma : Fin n -> CommonTerm m) -> (env : CommonSubstitutionTyped source target sigma) ->
  (decls : CommonDeclarations source paths) ->
  CommonFaceEqual decls face x y a ->
  CommonFaceEqual (substituteCommonDeclarations sigma env decls) face
    (substituteCommonPath sigma x) (substituteCommonPath sigma y) a
substituteCommonFaceEqual sigma env decls (CommonRefl typed) = CommonRefl (substituteCommonPathTyped sigma env typed)
substituteCommonFaceEqual sigma env decls (CommonSym eq) = CommonSym (substituteCommonFaceEqual sigma env decls eq)
substituteCommonFaceEqual sigma env decls (CommonTrans x y) = CommonTrans (substituteCommonFaceEqual sigma env decls x) (substituteCommonFaceEqual sigma env decls y)
substituteCommonFaceEqual sigma env decls (CommonLeft p check) = CommonLeft (substituteCommonDeclaredPath sigma env decls p) check
substituteCommonFaceEqual sigma env decls (CommonRight p check) = CommonRight (substituteCommonDeclaredPath sigma env decls p) check
substituteCommonFaceEqual sigma env decls (CommonRestrict eq check) = CommonRestrict (substituteCommonFaceEqual sigma env decls eq) check
substituteCommonFaceEqual sigma env decls (CommonAppEqual f x) = CommonAppEqual (substituteCommonFaceEqual sigma env decls f) (substituteCommonFaceEqual sigma env decls x)
substituteCommonFaceEqual sigma env decls (CommonIfEqual c t f) = CommonIfEqual (substituteCommonFaceEqual sigma env decls c) (substituteCommonFaceEqual sigma env decls t) (substituteCommonFaceEqual sigma env decls f)
substituteCommonFaceEqual sigma env decls (CommonUnitElimEqual x b) = CommonUnitElimEqual (substituteCommonFaceEqual sigma env decls x) (substituteCommonFaceEqual sigma env decls b)

public export
commonDeclaredEndpoint : {0 decls : PathDeclarations ctx paths} -> {0 face : ScopedFace d} ->
  {0 x, y : PathBody ctx paths d a} -> DeclaredEndpoint decls face x y ->
  CommonFaceEqual (commonDeclarations decls) face (commonPathTerm x) (commonPathTerm y) a
commonDeclaredEndpoint (DeclaredLeft p check) = CommonLeft (commonDeclaredPath p) check
commonDeclaredEndpoint (DeclaredRight p check) = CommonRight (commonDeclaredPath p) check

public export
commonBodyEqual : {0 decls : PathDeclarations ctx paths} -> {0 face : ScopedFace d} ->
  {0 x, y : PathBody ctx paths d a} -> BodyEqual decls face x y ->
  CommonFaceEqual (commonDeclarations decls) face (commonPathTerm x) (commonPathTerm y) a
commonBodyEqual {x} BodyRefl = CommonRefl (commonPathTermTyped x)
commonBodyEqual (BodySym eq) = CommonSym (commonBodyEqual eq)
commonBodyEqual (BodyTrans x y) = CommonTrans (commonBodyEqual x) (commonBodyEqual y)
commonBodyEqual (BodyEndpoint eq) = commonDeclaredEndpoint eq
commonBodyEqual (BodyRestrict eq check) = CommonRestrict (commonBodyEqual eq) check
commonBodyEqual (BodyAppEqual f x) = CommonAppEqual (commonBodyEqual f) (commonBodyEqual x)
commonBodyEqual (BodyIfEqual c t f) = CommonIfEqual (commonBodyEqual c) (commonBodyEqual t) (commonBodyEqual f)
commonBodyEqual (BodyUnitElimEqual x b) = CommonUnitElimEqual (commonBodyEqual x) (commonBodyEqual b)

||| A common abstraction has independently typed endpoints and actual boundaries.
public export
data CommonShadowPath : {0 ctx : Vect n LogicalType} -> {0 paths : Vect k LogicalType} ->
  CommonDeclarations ctx paths -> ScopedFace d -> CommonPathTerm n k d -> CommonPathTerm n k d -> (0 ty : LogicalType) -> Type where
  CommonAbstract : {0 ctx : Vect n LogicalType} -> {0 paths : Vect k LogicalType} ->
    {0 decls : CommonDeclarations ctx paths} -> {0 face : ScopedFace d} ->
    {0 left, right : CommonPathTerm n k d} ->
    (0 leftType : CommonPathHasType ctx paths left a) ->
    (0 rightType : CommonPathHasType ctx paths right a) ->
    (body : CommonPathTerm n k (S d)) ->
    (0 bodyType : CommonPathHasType ctx paths body a) ->
    CommonFaceEqual decls (SConjunction (weakenFace face) (SEndpoint FZ False))
      body (mapCommonPathDimensions (Var . FS) left) a ->
    CommonFaceEqual decls (SConjunction (weakenFace face) (SEndpoint FZ True))
      body (mapCommonPathDimensions (Var . FS) right) a ->
    CommonShadowPath decls face left right a

public export
substituteCommonShadowPath : {0 source : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  (sigma : Fin n -> CommonTerm m) -> (env : CommonSubstitutionTyped source target sigma) ->
  (decls : CommonDeclarations source paths) -> {0 left, right : CommonPathTerm n k d} ->
  CommonShadowPath decls face left right a ->
  CommonShadowPath (substituteCommonDeclarations sigma env decls) face
    (substituteCommonPath sigma left) (substituteCommonPath sigma right) a
substituteCommonShadowPath sigma env decls {left} {right} (CommonAbstract lt rt body bt zero one) =
  CommonAbstract (substituteCommonPathTyped sigma env lt) (substituteCommonPathTyped sigma env rt)
    (substituteCommonPath sigma body) (substituteCommonPathTyped sigma env bt)
    (rewrite commonPathMixedSubstitution sigma (Var . FS) left in substituteCommonFaceEqual sigma env decls zero)
    (rewrite commonPathMixedSubstitution sigma (Var . FS) right in substituteCommonFaceEqual sigma env decls one)

public export
commonDeclaredShadowPath : {0 decls : PathDeclarations ctx paths} -> {0 face : ScopedFace d} ->
  {0 left, right : PathBody ctx paths d a} ->
  DeclaredShadowPath decls face left right ->
  CommonShadowPath (commonDeclarations decls) face (commonPathTerm left) (commonPathTerm right) a
commonDeclaredShadowPath {left} {right} (ShadowAbstract body zero one) =
  CommonAbstract (commonPathTermTyped left) (commonPathTermTyped right) (commonPathTerm body)
    (commonPathTermTyped body)
    (rewrite sym (commonPathDimensionsCommute (Var . FS) left) in commonBodyEqual zero)
    (rewrite sym (commonPathDimensionsCommute (Var . FS) right) in commonBodyEqual one)

public export
applyCommonShadowPath : {0 ctx : Vect n LogicalType} -> {0 paths : Vect k LogicalType} ->
  {0 decls : CommonDeclarations ctx paths} -> {0 face : ScopedFace d} ->
  {0 left, right : CommonPathTerm n k d} ->
  CommonShadowPath decls face left right a -> ScopedInterval d -> CommonPathTerm n k d
applyCommonShadowPath (CommonAbstract _ _ body _ _ _) i = mapCommonPathDimensions (atDimension i) body

public export
substituteCommonShadowApplication : {0 source : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  (sigma : Fin n -> CommonTerm m) -> (env : CommonSubstitutionTyped source target sigma) ->
  (decls : CommonDeclarations source paths) -> {0 left, right : CommonPathTerm n k d} ->
  (path : CommonShadowPath decls face left right a) -> (i : ScopedInterval d) ->
  applyCommonShadowPath (substituteCommonShadowPath sigma env decls path) i =
    substituteCommonPath sigma (applyCommonShadowPath path i)
substituteCommonShadowApplication sigma env decls (CommonAbstract lt rt body bt zero one) i =
  commonPathMixedSubstitution sigma (atDimension i) body

public export
commonShadowApplicationCommutes : {0 decls : PathDeclarations ctx paths} -> {0 face : ScopedFace d} ->
  {0 left, right : PathBody ctx paths d a} -> (path : DeclaredShadowPath decls face left right) ->
  (i : ScopedInterval d) ->
  commonPathTerm (applyDeclaredShadowPath path i) = applyCommonShadowPath (commonDeclaredShadowPath path) i
commonShadowApplicationCommutes (ShadowAbstract body zero one) i = commonPathDimensionsCommute (atDimension i) body

public export
commonShadowApplicationZero : {0 decls : PathDeclarations ctx paths} -> {0 face : ScopedFace d} ->
  {0 left, right : PathBody ctx paths d a} -> (path : DeclaredShadowPath decls face left right) ->
  ZeroApplicationEvidence face left right path ->
  CommonFaceEqual (commonDeclarations decls) face (applyCommonShadowPath (commonDeclaredShadowPath path) Zero) (commonPathTerm left) a
commonShadowApplicationZero (ShadowAbstract body zero one) cert =
  rewrite sym (commonPathDimensionsCommute (atDimension Zero) body) in commonBodyEqual (declaredShadowAtZero body zero one cert)

public export
commonShadowApplicationOne : {0 decls : PathDeclarations ctx paths} -> {0 face : ScopedFace d} ->
  {0 left, right : PathBody ctx paths d a} -> (path : DeclaredShadowPath decls face left right) ->
  OneApplicationEvidence face left right path ->
  CommonFaceEqual (commonDeclarations decls) face (applyCommonShadowPath (commonDeclaredShadowPath path) One) (commonPathTerm right) a
commonShadowApplicationOne (ShadowAbstract body zero one) cert =
  rewrite sym (commonPathDimensionsCommute (atDimension One) body) in commonBodyEqual (declaredShadowAtOne body zero one cert)

||| The quantitative result is obtained from the source derivations, not from
||| shadow equality. The path uses the very same single source substitution.
public export
commonQuantitativeSubstitution : {n : Nat} ->
  (source : Vect (S n) Ty) -> {0 target : Vect n Ty} ->
  (s : SingleSubstitution source target) -> (term : Term source a) ->
  (usage : Usage (S n)) -> Uses term usage ->
  (replacement : Usage n) -> ReplacementUses s replacement ->
  {0 paths : Vect k LogicalType} -> {0 face : ScopedFace d} ->
  {0 decls : PathDeclarations (shadowContext source) paths} ->
  {0 left, right : PathBody (shadowContext source) paths d b} ->
  (path : DeclaredShadowPath decls face left right) ->
  (SubstitutionResult s term usage replacement,
   CommonHasType (shadowContext target)
     (commonTerm (shadowTerm (substitute (singleSubstitution s) term))) (shadowType a),
   CommonShadowPath
     (commonDeclarations (substitutePathDeclarations (imageSubstitution source (singleSubstitution s)) decls)) face
     (commonPathTerm (mapPathTerms (imageSubstitution source (singleSubstitution s)) left))
     (commonPathTerm (mapPathTerms (imageSubstitution source (singleSubstitution s)) right)) b)
commonQuantitativeSubstitution source s term usage used replacement replacementUsed path =
  (substituteUses s term usage used replacement replacementUsed,
   sourceCommonTyped (substitute (singleSubstitution s) term),
   commonDeclaredShadowPath (substituteDeclaredShadowPath (imageSubstitution source (singleSubstitution s)) path))

||| Source usage and the independent common path use the same substitution.
public export
commonQuantitativeIndependentPath : {n : Nat} ->
  (source : Vect (S n) Ty) -> {0 target : Vect n Ty} ->
  (s : SingleSubstitution source target) -> (term : Term source a) ->
  (usage : Usage (S n)) -> Uses term usage ->
  (replacement : Usage n) -> ReplacementUses s replacement ->
  (decls : CommonDeclarations (shadowContext source) paths) ->
  {0 face : ScopedFace d} -> {0 left, right : CommonPathTerm (S n) k d} ->
  CommonShadowPath decls face left right b ->
  (SubstitutionResult s term usage replacement,
   commonTerm (shadowTerm (substitute (singleSubstitution s) term)) =
     substituteCommon (commonImageSubstitution (shadowContext source) (imageSubstitution source (singleSubstitution s))) (commonTerm (shadowTerm term)),
   CommonShadowPath
     (substituteCommonDeclarations (commonImageSubstitution (shadowContext source) (imageSubstitution source (singleSubstitution s)))
       (commonImageSubstitutionTyped (shadowContext source) (imageSubstitution source (singleSubstitution s))) decls) face
     (substituteCommonPath (commonImageSubstitution (shadowContext source) (imageSubstitution source (singleSubstitution s))) left)
     (substituteCommonPath (commonImageSubstitution (shadowContext source) (imageSubstitution source (singleSubstitution s))) right) b)
commonQuantitativeIndependentPath source s term usage used replacement replacementUsed decls path =
  (substituteUses s term usage used replacement replacementUsed,
   sourceIndependentCommonSubstitution source (singleSubstitution s) term,
   substituteCommonShadowPath (commonImageSubstitution (shadowContext source) (imageSubstitution source (singleSubstitution s)))
     (commonImageSubstitutionTyped (shadowContext source) (imageSubstitution source (singleSubstitution s))) decls path)

||| Semantic carriers deliberately have no inhabitants at arrow types.
public export
FirstOrderValue : LogicalType -> Type
FirstOrderValue LUnit = Builtin.Unit
FirstOrderValue LBool = Bool
FirstOrderValue (LArrow _ _) = Void

||| A finite, type-indexed ordinary environment.
public export
data FirstOrderEnv : Vect n LogicalType -> Type where
  FONil : FirstOrderEnv []
  FOCons : FirstOrderValue a -> FirstOrderEnv ctx -> FirstOrderEnv (a :: ctx)

public export
firstOrderLookup : LogicalVar ctx a -> FirstOrderEnv ctx -> FirstOrderValue a
firstOrderLookup LHere (FOCons x xs) = x
firstOrderLookup (LThere v) (FOCons x xs) = firstOrderLookup v xs

||| Structural evidence excludes lambda and application, including those hidden
||| inside an embedded ordinary term. It is indexed by the actual typing proof.
public export
data FirstOrderTerm : {0 ctx : Vect n LogicalType} -> {0 t : CommonTerm n} ->
  {0 a : LogicalType} -> (0 typing : CommonHasType ctx t a) -> Type where
  FOVar : (v : LogicalVar ctx a) -> FirstOrderTerm (CVariable v)
  FOUnit : FirstOrderTerm CUnitType
  FOBool : {0 ctx : Vect n LogicalType} -> (b : Bool) -> FirstOrderTerm {ctx = ctx} (CBoolType {b})
  FOUnitElim : {0 x : CommonHasType ctx xt LUnit} -> {0 b : CommonHasType ctx bt a} -> FirstOrderTerm x -> FirstOrderTerm b ->
    FirstOrderTerm (CUnitEliminationType x b)
  FOIf : {0 c : CommonHasType ctx ct LBool} -> {0 t : CommonHasType ctx tt a} -> {0 f : CommonHasType ctx ft a} -> FirstOrderTerm c -> FirstOrderTerm t -> FirstOrderTerm f ->
    FirstOrderTerm (CConditionalType c t f)

public export
interpretFirstOrderTerm : {0 typing : CommonHasType ctx t a} ->
  FirstOrderTerm typing -> FirstOrderEnv ctx -> FirstOrderValue a
interpretFirstOrderTerm (FOVar v) env = firstOrderLookup v env
interpretFirstOrderTerm FOUnit env = ()
interpretFirstOrderTerm (FOBool b) env = b
interpretFirstOrderTerm (FOUnitElim x b) env = interpretFirstOrderTerm b env
interpretFirstOrderTerm (FOIf c t f) env =
  if interpretFirstOrderTerm c env then interpretFirstOrderTerm t env else interpretFirstOrderTerm f env

||| Each named path is a function of the actual four-pair dimension value.
||| It may also depend on the whole ordinary environment.
public export
data FirstOrderPaths : Vect n LogicalType -> Vect k LogicalType -> Type where
  FONoPaths : FirstOrderPaths ctx []
  FOPath : (FirstOrderEnv ctx -> DM -> FirstOrderValue a) ->
    FirstOrderPaths ctx paths -> FirstOrderPaths ctx (a :: paths)

public export
firstOrderPathLookup : LogicalVar paths a -> FirstOrderPaths ctx paths ->
  FirstOrderEnv ctx -> DM -> FirstOrderValue a
firstOrderPathLookup LHere (FOPath p rest) = p
firstOrderPathLookup (LThere v) (FOPath p rest) = firstOrderPathLookup v rest

public export
data FirstOrderPathTerm : {0 ctx : Vect n LogicalType} -> {0 paths : Vect k LogicalType} ->
  {0 t : CommonPathTerm n k d} -> {0 a : LogicalType} ->
  (0 typing : CommonPathHasType ctx paths t a) -> Type where
  FOOrdinary : {0 paths : Vect k LogicalType} -> {0 t : CommonHasType ctx tm a} -> FirstOrderTerm t -> FirstOrderPathTerm {paths = paths} (CPOrdinaryType t)
  FOAt : {0 ctx : Vect n LogicalType} -> (p : LogicalVar paths a) -> (i : ScopedInterval d) -> FirstOrderPathTerm {ctx = ctx} (CPAtType {i} p)
  FOPathUnitElim : {0 x : CommonPathHasType ctx paths xt LUnit} -> {0 b : CommonPathHasType ctx paths bt a} -> FirstOrderPathTerm x -> FirstOrderPathTerm b ->
    FirstOrderPathTerm (CPUnitElimType x b)
  FOPathIf : {0 c : CommonPathHasType ctx paths ct LBool} -> {0 t : CommonPathHasType ctx paths tt a} -> {0 f : CommonPathHasType ctx paths ft a} -> FirstOrderPathTerm c -> FirstOrderPathTerm t -> FirstOrderPathTerm f ->
    FirstOrderPathTerm (CPIfType c t f)

||| No first-order witness exists for an application typing derivation.
public export
firstOrderPathApplicationImpossible : {0 f : CommonPathHasType ctx paths fn (LArrow a b)} ->
  {0 x : CommonPathHasType ctx paths arg a} -> FirstOrderPathTerm (CPAppType f x) -> Void
firstOrderPathApplicationImpossible w impossible

public export
interpretFirstOrderPath : {0 t : CommonPathTerm n k d} -> {0 typing : CommonPathHasType ctx paths t a} ->
  FirstOrderPathTerm typing -> FirstOrderEnv ctx -> FirstOrderPaths ctx paths ->
  (Fin d -> DM) -> FirstOrderValue a
interpretFirstOrderPath (FOOrdinary t) env paths valuation = interpretFirstOrderTerm t env
interpretFirstOrderPath (FOAt p i) env paths valuation =
  firstOrderPathLookup p paths env (evalDMVal valuation i)
interpretFirstOrderPath (FOPathUnitElim x b) env paths valuation =
  interpretFirstOrderPath b env paths valuation
interpretFirstOrderPath (FOPathIf c t f) env paths valuation =
  if interpretFirstOrderPath c env paths valuation
     then interpretFirstOrderPath t env paths valuation
     else interpretFirstOrderPath f env paths valuation

||| Admissibility relates each actual declared endpoint to its interpretation
||| for every ordinary environment, not merely a chosen valuation.
public export
data FirstOrderAdmissible : {0 ctx : Vect n LogicalType} ->
  {0 paths : Vect k LogicalType} -> CommonDeclarations ctx paths ->
  FirstOrderPaths ctx paths -> Type where
  FOAdmissibleNil : FirstOrderAdmissible CommonNoPaths FONoPaths
  FOAdmissibleCons : {0 paths : Vect k LogicalType} -> {rest : CommonDeclarations ctx paths} -> {ps : FirstOrderPaths ctx paths} -> {0 lt : CommonHasType ctx l a} -> {0 rt : CommonHasType ctx r a} ->
    (left : FirstOrderTerm lt) -> (right : FirstOrderTerm rt) ->
    {path : FirstOrderEnv ctx -> DM -> FirstOrderValue a} ->
    ((env : FirstOrderEnv ctx) -> path env (False, False) = interpretFirstOrderTerm left env) ->
    ((env : FirstOrderEnv ctx) -> path env (True, True) = interpretFirstOrderTerm right env) ->
    FirstOrderAdmissible rest ps ->
    FirstOrderAdmissible (CommonDeclarePath l r lt rt rest) (FOPath path ps)

||| Endpoint witnesses retain erased typing derivations without recovering them
||| from erased declaration fields at runtime.
public export
data FirstOrderEndpoints : {0 ctx : Vect n LogicalType} -> {0 paths : Vect k LogicalType} ->
  (p : LogicalVar paths a) -> (l, r : CommonTerm n) -> FirstOrderPaths ctx paths -> Type where
  FOEndpoints : {0 paths : Vect k LogicalType} -> {p : LogicalVar paths a} -> {ps : FirstOrderPaths ctx paths} -> {0 lt : CommonHasType ctx l a} -> {0 rt : CommonHasType ctx r a} ->
    (left : FirstOrderTerm lt) -> (right : FirstOrderTerm rt) ->
    ((env : FirstOrderEnv ctx) -> firstOrderPathLookup p ps env (False, False) = interpretFirstOrderTerm left env) ->
    ((env : FirstOrderEnv ctx) -> firstOrderPathLookup p ps env (True, True) = interpretFirstOrderTerm right env) ->
    FirstOrderEndpoints p l r ps

public export
firstOrderDeclaredLookup : {0 decls : CommonDeclarations ctx paths} ->
  {p : LogicalVar paths a} -> {l, r : CommonTerm n} ->
  CommonDeclaredPath decls p l r -> (ps : FirstOrderPaths ctx paths) ->
  FirstOrderAdmissible decls ps -> FirstOrderEndpoints p l r ps
firstOrderDeclaredLookup CommonDeclaredHere (FOPath path ps) (FOAdmissibleCons left right zero one rest) =
  FOEndpoints left right zero one
firstOrderDeclaredLookup (CommonDeclaredThere declared) (FOPath path ps) (FOAdmissibleCons left right zero one rest) =
  case firstOrderDeclaredLookup declared ps rest of
    FOEndpoints l r z o => FOEndpoints l r z o

||| Face entailment remains sound under the same four-pair valuation.
public export
commonFaceValEntailsSound : {d : Nat} -> (valuation : Fin d -> DM) -> (face, source : ScopedFace d) ->
  boundedFaceEntails face source = True -> faceAtVal valuation face = True ->
  faceAtVal valuation source = True
commonFaceValEntailsSound valuation face source accepted holds =
  rewrite sym (commonFaceValAgreement valuation source) in
  boundedFaceEntailsSound (\i, b => valuation i == (b, b)) face source accepted
    (rewrite commonFaceValAgreement valuation face in holds)

||| The endpoint witness comes from the declaration's admissibility evidence.
public export
data FirstOrderLeftAtFace : {0 ctx : Vect n LogicalType} ->
  {0 paths : Vect k LogicalType} -> (p : LogicalVar paths a) ->
  (l : CommonTerm n) -> (ps : FirstOrderPaths ctx paths) ->
  (env : FirstOrderEnv ctx) -> (value : DM) -> Type where
  FOLeftAtFace : {0 paths : Vect k LogicalType} -> {p : LogicalVar paths a} -> {ps : FirstOrderPaths ctx paths} -> {0 lt : CommonHasType ctx l a} -> (left : FirstOrderTerm lt) ->
    firstOrderPathLookup p ps env value = interpretFirstOrderTerm left env ->
    FirstOrderLeftAtFace p l ps env value

public export
firstOrderDeclaredLeftAtFace : {0 decls : CommonDeclarations ctx paths} ->
  {p : LogicalVar paths a} -> {l, r : CommonTerm n} ->
  CommonDeclaredPath decls p l r -> (ps : FirstOrderPaths ctx paths) ->
  FirstOrderAdmissible decls ps -> (env : FirstOrderEnv ctx) ->
  (valuation : Fin d -> DM) -> (face : ScopedFace d) -> (i : ScopedInterval d) ->
  boundedEndpointEntails face i False = True -> faceAtVal valuation face = True ->
  FirstOrderLeftAtFace p l ps env (evalDMVal valuation i)
firstOrderDeclaredLeftAtFace declared ps admissible env valuation face i accepted holds =
  case firstOrderDeclaredLookup declared ps admissible of
    FOEndpoints left right zero one =>
      FOLeftAtFace left (rewrite commonBoundedEndpointValSound valuation face i False accepted holds in zero env)

||| Right endpoint counterpart, retaining its actual first-order term witness.
public export
data FirstOrderRightAtFace : {0 ctx : Vect n LogicalType} ->
  {0 paths : Vect k LogicalType} -> (p : LogicalVar paths a) ->
  (r : CommonTerm n) -> (ps : FirstOrderPaths ctx paths) ->
  (env : FirstOrderEnv ctx) -> (value : DM) -> Type where
  FORightAtFace : {0 paths : Vect k LogicalType} -> {p : LogicalVar paths a} -> {ps : FirstOrderPaths ctx paths} -> {0 rt : CommonHasType ctx r a} -> (right : FirstOrderTerm rt) ->
    firstOrderPathLookup p ps env value = interpretFirstOrderTerm right env ->
    FirstOrderRightAtFace p r ps env value

public export
firstOrderDeclaredRightAtFace : {0 decls : CommonDeclarations ctx paths} ->
  {p : LogicalVar paths a} -> {l, r : CommonTerm n} ->
  CommonDeclaredPath decls p l r -> (ps : FirstOrderPaths ctx paths) ->
  FirstOrderAdmissible decls ps -> (env : FirstOrderEnv ctx) ->
  (valuation : Fin d -> DM) -> (face : ScopedFace d) -> (i : ScopedInterval d) ->
  boundedEndpointEntails face i True = True -> faceAtVal valuation face = True ->
  FirstOrderRightAtFace p r ps env (evalDMVal valuation i)
firstOrderDeclaredRightAtFace declared ps admissible env valuation face i accepted holds =
  case firstOrderDeclaredLookup declared ps admissible of
    FOEndpoints left right zero one =>
      FORightAtFace right (rewrite commonBoundedEndpointValSound valuation face i True accepted holds in one env)

public export
firstOrderLookupCoherent : (v, w : LogicalVar ctx a) ->
  variableIndex v = variableIndex w -> (env : FirstOrderEnv ctx) ->
  firstOrderLookup v env = firstOrderLookup w env
firstOrderLookupCoherent LHere LHere Refl (FOCons x xs) = Refl
firstOrderLookupCoherent (LThere v) (LThere w) eq (FOCons x xs) = firstOrderLookupCoherent v w (injective eq) xs
firstOrderLookupCoherent LHere (LThere w) Refl env impossible
firstOrderLookupCoherent (LThere v) LHere Refl env impossible

public export
firstOrderTermSyntax : {0 t : CommonTerm n} -> {0 typing : CommonHasType ctx t a} -> FirstOrderTerm typing -> CommonTerm n
firstOrderTermSyntax (FOVar v) = CVar (variableIndex v)
firstOrderTermSyntax FOUnit = CUnit
firstOrderTermSyntax (FOBool b) = CBool b
firstOrderTermSyntax (FOUnitElim x b) = CUnitElim (firstOrderTermSyntax x) (firstOrderTermSyntax b)
firstOrderTermSyntax (FOIf c t f) = CIf (firstOrderTermSyntax c) (firstOrderTermSyntax t) (firstOrderTermSyntax f)

public export
firstOrderTermSyntaxCorrect : {0 t : CommonTerm n} -> {0 typing : CommonHasType ctx t a} ->
  (x : FirstOrderTerm typing) -> firstOrderTermSyntax x = t
firstOrderTermSyntaxCorrect (FOVar v) = Refl
firstOrderTermSyntaxCorrect FOUnit = Refl
firstOrderTermSyntaxCorrect (FOBool b) = Refl
firstOrderTermSyntaxCorrect (FOUnitElim x b) = rewrite firstOrderTermSyntaxCorrect x in rewrite firstOrderTermSyntaxCorrect b in Refl
firstOrderTermSyntaxCorrect (FOIf c t f) = rewrite firstOrderTermSyntaxCorrect c in rewrite firstOrderTermSyntaxCorrect t in rewrite firstOrderTermSyntaxCorrect f in Refl

commonVarInjective : CVar x = CVar y -> x = y
commonVarInjective Refl = Refl

commonBoolInjective : CBool x = CBool y -> x = y
commonBoolInjective Refl = Refl

commonUnitBodyInjective : CUnitElim x b = CUnitElim y c -> b = c
commonUnitBodyInjective Refl = Refl

commonIfCondInjective : CIf c t f = CIf c1 t1 f1 -> c = c1
commonIfCondInjective Refl = Refl

commonIfThenInjective : CIf c t f = CIf c1 t1 f1 -> t = t1
commonIfThenInjective Refl = Refl

commonIfElseInjective : CIf c t f = CIf c1 t1 f1 -> f = f1
commonIfElseInjective Refl = Refl

public export
firstOrderTermSyntaxCoherent : {0 l : CommonHasType ctx lt a} -> {0 r : CommonHasType ctx rt a} ->
  (x : FirstOrderTerm l) -> (y : FirstOrderTerm r) ->
  firstOrderTermSyntax x = firstOrderTermSyntax y -> (env : FirstOrderEnv ctx) ->
  interpretFirstOrderTerm x env = interpretFirstOrderTerm y env
firstOrderTermSyntaxCoherent (FOVar v) (FOVar w) eq env = firstOrderLookupCoherent v w (commonVarInjective eq) env
firstOrderTermSyntaxCoherent FOUnit FOUnit eq env = Refl
firstOrderTermSyntaxCoherent (FOBool b) (FOBool c) eq env = commonBoolInjective eq
firstOrderTermSyntaxCoherent (FOUnitElim x b) (FOUnitElim y c) eq env = firstOrderTermSyntaxCoherent b c (commonUnitBodyInjective eq) env
firstOrderTermSyntaxCoherent (FOIf c t f) (FOIf c' t' f') eq env with (interpretFirstOrderTerm c env) proof choice
  firstOrderTermSyntaxCoherent (FOIf c t f) (FOIf c' t' f') eq env | True =
    rewrite sym (firstOrderTermSyntaxCoherent c c' (commonIfCondInjective eq) env) in
    rewrite choice in firstOrderTermSyntaxCoherent t t' (commonIfThenInjective eq) env
  firstOrderTermSyntaxCoherent (FOIf c t f) (FOIf c' t' f') eq env | False =
    rewrite sym (firstOrderTermSyntaxCoherent c c' (commonIfCondInjective eq) env) in
    rewrite choice in firstOrderTermSyntaxCoherent f f' (commonIfElseInjective eq) env

public export
firstOrderTermCoherent : {0 t : CommonTerm n} -> {0 l, r : CommonHasType ctx t a} ->
  (x : FirstOrderTerm l) -> (y : FirstOrderTerm r) -> (env : FirstOrderEnv ctx) ->
  interpretFirstOrderTerm x env = interpretFirstOrderTerm y env
firstOrderTermCoherent x y env = firstOrderTermSyntaxCoherent x y
  (trans (firstOrderTermSyntaxCorrect x) (sym (firstOrderTermSyntaxCorrect y))) env

public export
firstOrderPathLookupCoherent : (v, w : LogicalVar paths a) ->
  variableIndex v = variableIndex w -> (ps : FirstOrderPaths ctx paths) ->
  (env : FirstOrderEnv ctx) -> (value : DM) ->
  firstOrderPathLookup v ps env value = firstOrderPathLookup w ps env value
firstOrderPathLookupCoherent LHere LHere Refl (FOPath p ps) env value = Refl
firstOrderPathLookupCoherent (LThere v) (LThere w) eq (FOPath p ps) env value =
  firstOrderPathLookupCoherent v w (injective eq) ps env value
firstOrderPathLookupCoherent LHere (LThere w) Refl ps env value impossible
firstOrderPathLookupCoherent (LThere v) LHere Refl ps env value impossible

public export
firstOrderPathSyntax : {0 t : CommonPathTerm n k d} -> {0 typing : CommonPathHasType ctx paths t a} ->
  FirstOrderPathTerm typing -> CommonPathTerm n k d
firstOrderPathSyntax (FOOrdinary t) = CPOrdinary (firstOrderTermSyntax t)
firstOrderPathSyntax (FOAt p i) = CPAt (variableIndex p) i
firstOrderPathSyntax (FOPathUnitElim x b) = CPUnitElim (firstOrderPathSyntax x) (firstOrderPathSyntax b)
firstOrderPathSyntax (FOPathIf c t f) = CPIf (firstOrderPathSyntax c) (firstOrderPathSyntax t) (firstOrderPathSyntax f)

public export
firstOrderPathSyntaxCorrect : {0 t : CommonPathTerm n k d} -> {0 typing : CommonPathHasType ctx paths t a} ->
  (x : FirstOrderPathTerm typing) -> firstOrderPathSyntax x = t
firstOrderPathSyntaxCorrect (FOOrdinary t) = cong CPOrdinary (firstOrderTermSyntaxCorrect t)
firstOrderPathSyntaxCorrect (FOAt p i) = Refl
firstOrderPathSyntaxCorrect (FOPathUnitElim x b) = rewrite firstOrderPathSyntaxCorrect x in rewrite firstOrderPathSyntaxCorrect b in Refl
firstOrderPathSyntaxCorrect (FOPathIf c t f) = rewrite firstOrderPathSyntaxCorrect c in rewrite firstOrderPathSyntaxCorrect t in rewrite firstOrderPathSyntaxCorrect f in Refl

commonPathOrdinaryInjective : CPOrdinary x = CPOrdinary y -> x = y
commonPathOrdinaryInjective Refl = Refl
commonPathAtIndexInjective : CPAt x i = CPAt y j -> x = y
commonPathAtIndexInjective Refl = Refl
commonPathAtIntervalInjective : CPAt x i = CPAt y j -> i = j
commonPathAtIntervalInjective Refl = Refl
commonPathUnitBodyInjective : CPUnitElim x b = CPUnitElim y c -> b = c
commonPathUnitBodyInjective Refl = Refl
commonPathIfCondInjective : CPIf c t f = CPIf c1 t1 f1 -> c = c1
commonPathIfCondInjective Refl = Refl
commonPathIfThenInjective : CPIf c t f = CPIf c1 t1 f1 -> t = t1
commonPathIfThenInjective Refl = Refl
commonPathIfElseInjective : CPIf c t f = CPIf c1 t1 f1 -> f = f1
commonPathIfElseInjective Refl = Refl

public export
firstOrderPathSyntaxCoherent : {0 l : CommonPathHasType ctx paths lt a} -> {0 r : CommonPathHasType ctx paths rt a} ->
  (x : FirstOrderPathTerm l) -> (y : FirstOrderPathTerm r) ->
  firstOrderPathSyntax x = firstOrderPathSyntax y -> (env : FirstOrderEnv ctx) ->
  (ps : FirstOrderPaths ctx paths) -> (valuation : Fin d -> DM) ->
  interpretFirstOrderPath x env ps valuation = interpretFirstOrderPath y env ps valuation
firstOrderPathSyntaxCoherent (FOOrdinary x) (FOOrdinary y) eq env ps valuation =
  firstOrderTermSyntaxCoherent x y (commonPathOrdinaryInjective eq) env
firstOrderPathSyntaxCoherent (FOAt p i) (FOAt q j) eq env ps valuation =
  rewrite sym (commonPathAtIntervalInjective eq) in
  firstOrderPathLookupCoherent p q (commonPathAtIndexInjective eq) ps env (evalDMVal valuation i)
firstOrderPathSyntaxCoherent (FOPathUnitElim x b) (FOPathUnitElim y c) eq env ps valuation =
  firstOrderPathSyntaxCoherent b c (commonPathUnitBodyInjective eq) env ps valuation
firstOrderPathSyntaxCoherent (FOPathIf c t f) (FOPathIf c' t' f') eq env ps valuation with (interpretFirstOrderPath c env ps valuation) proof choice
  firstOrderPathSyntaxCoherent (FOPathIf c t f) (FOPathIf c' t' f') eq env ps valuation | True =
    rewrite sym (firstOrderPathSyntaxCoherent c c' (commonPathIfCondInjective eq) env ps valuation) in
    rewrite choice in firstOrderPathSyntaxCoherent t t' (commonPathIfThenInjective eq) env ps valuation
  firstOrderPathSyntaxCoherent (FOPathIf c t f) (FOPathIf c' t' f') eq env ps valuation | False =
    rewrite sym (firstOrderPathSyntaxCoherent c c' (commonPathIfCondInjective eq) env ps valuation) in
    rewrite choice in firstOrderPathSyntaxCoherent f f' (commonPathIfElseInjective eq) env ps valuation

public export
firstOrderPathCoherent : {0 t : CommonPathTerm n k d} -> {0 l, r : CommonPathHasType ctx paths t a} ->
  (x : FirstOrderPathTerm l) -> (y : FirstOrderPathTerm r) -> (env : FirstOrderEnv ctx) ->
  (ps : FirstOrderPaths ctx paths) -> (valuation : Fin d -> DM) ->
  interpretFirstOrderPath x env ps valuation = interpretFirstOrderPath y env ps valuation
firstOrderPathCoherent x y env ps valuation = firstOrderPathSyntaxCoherent x y
  (trans (firstOrderPathSyntaxCorrect x) (sym (firstOrderPathSyntaxCorrect y))) env ps valuation

||| First-order evidence for a supported fragment of an actual face derivation.
||| The endpoint witnesses are explicit because typing derivations are erased.
public export
data FirstOrderFaceEqual : {0 ctx : Vect n LogicalType} -> {0 paths : Vect k LogicalType} ->
  {0 decls : CommonDeclarations ctx paths} -> {0 face : ScopedFace d} ->
  {0 x, y : CommonPathTerm n k d} -> {0 a : LogicalType} ->
  {0 lt : CommonPathHasType ctx paths x a} -> {0 rt : CommonPathHasType ctx paths y a} ->
  (0 eq : CommonFaceEqual decls face x y a) ->
  FirstOrderPathTerm lt -> FirstOrderPathTerm rt -> Type where
  FOFaceRefl : (w : FirstOrderPathTerm typed) -> FirstOrderFaceEqual (CommonRefl typed) w w
  FOFaceSym : FirstOrderFaceEqual eq l r -> FirstOrderFaceEqual (CommonSym eq) r l
  FOFaceTrans : {0 x, y, z : CommonPathTerm n k d} ->
    {0 decls : CommonDeclarations ctx paths} -> {0 face : ScopedFace d} ->
    {0 eq : CommonFaceEqual decls face x y a} -> {0 eq' : CommonFaceEqual decls face y z a} ->
    {0 lx : CommonPathHasType ctx paths x a} -> {0 rz : CommonPathHasType ctx paths z a} ->
    {l : FirstOrderPathTerm lx} -> {r : FirstOrderPathTerm rz} ->
    {0 mid, mid' : CommonPathHasType ctx paths y a} ->
    {m : FirstOrderPathTerm mid} -> {m' : FirstOrderPathTerm mid'} ->
    FirstOrderFaceEqual eq l m -> FirstOrderFaceEqual eq' m' r ->
    FirstOrderFaceEqual (CommonTrans eq eq') l r
  FOFaceIf :
    {0 ctx : Vect n LogicalType} -> {0 paths : Vect k LogicalType} ->
    {0 decls : CommonDeclarations ctx paths} -> {0 face : ScopedFace d} ->
    {0 c : CommonPathTerm n k d} -> {0 cty, csub : CommonPathHasType ctx paths c LBool} ->
    {0 c' : CommonPathTerm n k d} -> {0 c'ty, c'sub : CommonPathHasType ctx paths c' LBool} ->
    {0 t : CommonPathTerm n k d} -> {0 tty, tsub : CommonPathHasType ctx paths t a} ->
    {0 t' : CommonPathTerm n k d} -> {0 t'ty, t'sub : CommonPathHasType ctx paths t' a} ->
    {0 f : CommonPathTerm n k d} -> {0 fty, fsub : CommonPathHasType ctx paths f a} ->
    {0 f' : CommonPathTerm n k d} -> {0 f'ty, f'sub : CommonPathHasType ctx paths f' a} ->
    {0 ceq : CommonFaceEqual decls face c c' LBool} -> {0 teq : CommonFaceEqual decls face t t' a} ->
    {0 feq : CommonFaceEqual decls face f f' a} ->
    {cl : FirstOrderPathTerm csub} -> {cr : FirstOrderPathTerm c'sub} ->
    {tl : FirstOrderPathTerm tsub} -> {tr : FirstOrderPathTerm t'sub} ->
    {fl : FirstOrderPathTerm fsub} -> {fr : FirstOrderPathTerm f'sub} ->
    (c : FirstOrderPathTerm cty) -> (c' : FirstOrderPathTerm c'ty) ->
    (t : FirstOrderPathTerm tty) -> (t' : FirstOrderPathTerm t'ty) ->
    (f : FirstOrderPathTerm fty) -> (f' : FirstOrderPathTerm f'ty) ->
    FirstOrderFaceEqual ceq cl cr -> FirstOrderFaceEqual teq tl tr ->
    FirstOrderFaceEqual feq fl fr ->
    FirstOrderFaceEqual (CommonIfEqual ceq teq feq) (FOPathIf c t f) (FOPathIf c' t' f')
  FOFaceUnitElim :
    {0 ctx : Vect n LogicalType} -> {0 paths : Vect k LogicalType} ->
    {0 decls : CommonDeclarations ctx paths} -> {0 face : ScopedFace d} ->
    {0 x : CommonPathTerm n k d} -> {0 xty, xsub : CommonPathHasType ctx paths x LUnit} ->
    {0 y : CommonPathTerm n k d} -> {0 yty, ysub : CommonPathHasType ctx paths y LUnit} ->
    {0 b : CommonPathTerm n k d} -> {0 bty, bsub : CommonPathHasType ctx paths b a} ->
    {0 b' : CommonPathTerm n k d} -> {0 b'ty, b'sub : CommonPathHasType ctx paths b' a} ->
    {0 xeq : CommonFaceEqual decls face x y LUnit} -> {0 beq : CommonFaceEqual decls face b b' a} ->
    {xl : FirstOrderPathTerm xsub} -> {xr : FirstOrderPathTerm ysub} ->
    {bl : FirstOrderPathTerm bsub} -> {br : FirstOrderPathTerm b'sub} ->
    (x : FirstOrderPathTerm xty) -> (y : FirstOrderPathTerm yty) ->
    (b : FirstOrderPathTerm bty) -> (b' : FirstOrderPathTerm b'ty) ->
    FirstOrderFaceEqual xeq xl xr -> FirstOrderFaceEqual beq bl br ->
    FirstOrderFaceEqual (CommonUnitElimEqual xeq beq) (FOPathUnitElim x b) (FOPathUnitElim y b')
  FOFaceRestrict : {0 x, y : CommonPathTerm n k d} ->
    {0 lt : CommonPathHasType ctx paths x a} -> {0 rt : CommonPathHasType ctx paths y a} ->
    {l : FirstOrderPathTerm lt} -> {r : FirstOrderPathTerm rt} ->
    {0 decls : CommonDeclarations ctx paths} -> (face, source : ScopedFace d) ->
    {0 eq : CommonFaceEqual decls source x y a} -> (check : boundedFaceEntails face source = True) -> FirstOrderFaceEqual {face = source} eq l r ->
    FirstOrderFaceEqual {face} (CommonRestrict eq check) l r
  FOFaceLeft : {face : ScopedFace d} -> {l, r : CommonTerm n} -> {0 typed : CommonHasType ctx l a} ->
    (p : LogicalVar paths a) -> (i : ScopedInterval d) ->
    (w : FirstOrderTerm typed) -> (declared : CommonDeclaredPath decls p l r) ->
    (check : boundedEndpointEntails face i False = True) ->
    FirstOrderFaceEqual {face} (CommonLeft {i} declared check) (FOAt p i) (FOOrdinary w)
  FOFaceRight : {face : ScopedFace d} -> {l, r : CommonTerm n} -> {0 typed : CommonHasType ctx r a} ->
    (p : LogicalVar paths a) -> (i : ScopedInterval d) ->
    (w : FirstOrderTerm typed) -> (declared : CommonDeclaredPath decls p l r) ->
    (check : boundedEndpointEntails face i True = True) ->
    FirstOrderFaceEqual {face} (CommonRight {i} declared check) (FOAt p i) (FOOrdinary w)

public export
firstOrderFaceEqualSound : {d : Nat} -> {0 decls : CommonDeclarations ctx paths} -> {0 face : ScopedFace d} ->
  {0 x, y : CommonPathTerm n k d} ->
  {0 lt : CommonPathHasType ctx paths x a} -> {0 rt : CommonPathHasType ctx paths y a} ->
  {0 eq : CommonFaceEqual decls face x y a} -> {l : FirstOrderPathTerm lt} -> {r : FirstOrderPathTerm rt} ->
  FirstOrderFaceEqual eq l r -> (env : FirstOrderEnv ctx) -> (ps : FirstOrderPaths ctx paths) ->
  FirstOrderAdmissible decls ps -> (valuation : Fin d -> DM) -> faceAtVal valuation face = True ->
  interpretFirstOrderPath l env ps valuation = interpretFirstOrderPath r env ps valuation
firstOrderFaceEqualSound (FOFaceRefl w) env ps adm valuation holds = Refl
firstOrderFaceEqualSound (FOFaceSym eq) env ps adm valuation holds = sym (firstOrderFaceEqualSound eq env ps adm valuation holds)
firstOrderFaceEqualSound (FOFaceTrans {m} {m'} eq eq') env ps adm valuation holds =
  trans (firstOrderFaceEqualSound eq env ps adm valuation holds)
    (trans (firstOrderPathCoherent m m' env ps valuation) (firstOrderFaceEqualSound eq' env ps adm valuation holds))
firstOrderFaceEqualSound (FOFaceIf c c' t t' f f' {cl} {cr} {tl} {tr} {fl} {fr} ce te fe) env ps adm valuation holds with (interpretFirstOrderPath c env ps valuation) proof choice
  firstOrderFaceEqualSound (FOFaceIf c c' t t' f f' {cl} {cr} {tl} {tr} {fl} {fr} ce te fe) env ps adm valuation holds | True =
    rewrite sym (trans (firstOrderPathCoherent c cl env ps valuation) (trans (firstOrderFaceEqualSound ce env ps adm valuation holds) (firstOrderPathCoherent cr c' env ps valuation))) in
    rewrite choice in trans (firstOrderPathCoherent t tl env ps valuation) (trans (firstOrderFaceEqualSound te env ps adm valuation holds) (firstOrderPathCoherent tr t' env ps valuation))
  firstOrderFaceEqualSound (FOFaceIf c c' t t' f f' {cl} {cr} {tl} {tr} {fl} {fr} ce te fe) env ps adm valuation holds | False =
    rewrite sym (trans (firstOrderPathCoherent c cl env ps valuation) (trans (firstOrderFaceEqualSound ce env ps adm valuation holds) (firstOrderPathCoherent cr c' env ps valuation))) in
    rewrite choice in trans (firstOrderPathCoherent f fl env ps valuation) (trans (firstOrderFaceEqualSound fe env ps adm valuation holds) (firstOrderPathCoherent fr f' env ps valuation))
firstOrderFaceEqualSound (FOFaceUnitElim x y b b' {bl} {br} xe be) env ps adm valuation holds =
  trans (firstOrderPathCoherent b bl env ps valuation)
    (trans (firstOrderFaceEqualSound be env ps adm valuation holds) (firstOrderPathCoherent br b' env ps valuation))
firstOrderFaceEqualSound (FOFaceRestrict face source check eq) env ps adm valuation holds =
  firstOrderFaceEqualSound eq env ps adm valuation (commonFaceValEntailsSound valuation face source check holds)
firstOrderFaceEqualSound (FOFaceLeft p i w declared check) env ps adm valuation holds =
  case firstOrderDeclaredLeftAtFace declared ps adm env valuation _ i check holds of
    FOLeftAtFace left prf => trans prf (firstOrderTermCoherent left w env)
firstOrderFaceEqualSound (FOFaceRight p i w declared check) env ps adm valuation holds =
  case firstOrderDeclaredRightAtFace declared ps adm env valuation _ i check holds of
    FORightAtFace right prf => trans prf (firstOrderTermCoherent right w env)

||| A constructive setoid; equality of semantic functions is not Idris
||| function equality.
public export
record CommonSetoid where
  constructor MkCommonSetoid
  carrier : Type
  related : carrier -> carrier -> Type
  relationRefl : (x : carrier) -> related x x
  relationSym : {x, y : carrier} -> related x y -> related y x
  relationTrans : {x, y, z : carrier} -> related x y -> related y z -> related x z

||| A semantic function must preserve the input relation.
public export
record CommonMorphism (a, b : CommonSetoid) where
  constructor MkCommonMorphism
  applyMorphism : carrier a -> carrier b
  respectsRelation : {x, y : carrier a} -> related a x y ->
                     related b (applyMorphism x) (applyMorphism y)

||| Heterogeneous pointwise relation gives application congruence directly.
public export
morphismsRelated : {a, b : CommonSetoid} -> CommonMorphism a b -> CommonMorphism a b -> Type
morphismsRelated {a} {b} f g = (x, y : carrier a) -> related a x y ->
  related b (applyMorphism f x) (applyMorphism g y)

public export
morphismsTrans : {a, b : CommonSetoid} -> {f, g, h : CommonMorphism a b} ->
  morphismsRelated f g -> morphismsRelated g h -> morphismsRelated f h
morphismsTrans {a} {b} fg gh x y xy =
  relationTrans b (fg x x (relationRefl a x)) (gh x y xy)

public export
commonArrowSetoid : CommonSetoid -> CommonSetoid -> CommonSetoid
commonArrowSetoid a b = MkCommonSetoid (CommonMorphism a b) morphismsRelated
  (\f, x, y, xy => respectsRelation f xy)
  (\fg, x, y, xy => relationSym b (fg y x (relationSym a xy)))
  morphismsTrans

public export
commonBoolSetoid : CommonSetoid
commonBoolSetoid = MkCommonSetoid Bool (\x, y => x = y) (\x => Refl) (\p => sym p) (\p, q => trans p q)

public export
commonUnitSetoid : CommonSetoid
commonUnitSetoid = MkCommonSetoid Builtin.Unit (\x, y => x = y) (\x => Refl) (\p => sym p) (\p, q => trans p q)

||| Setoid interpretation of the logical type grammar.
public export
commonTypeSetoid : LogicalType -> CommonSetoid
commonTypeSetoid LBool = commonBoolSetoid
commonTypeSetoid LUnit = commonUnitSetoid
commonTypeSetoid (LArrow a b) = commonArrowSetoid (commonTypeSetoid a) (commonTypeSetoid b)

public export
commonApplicationCongruence : {a, b : CommonSetoid} ->
  {f, g : CommonMorphism a b} -> {x, y : carrier a} ->
  morphismsRelated f g -> related a x y -> related b (applyMorphism f x) (applyMorphism g y)
commonApplicationCongruence fg xy = fg _ _ xy

||| Product setoids retain pointwise evidence, including for arrow-valued entries.
public export
commonProductSetoid : CommonSetoid -> CommonSetoid -> CommonSetoid
commonProductSetoid a b = MkCommonSetoid (carrier a, carrier b)
  (\x, y => (related a (fst x) (fst y), related b (snd x) (snd y)))
  (\(x, y) => (relationRefl a x, relationRefl b y))
  (\(p, q) => (relationSym a p, relationSym b q))
  (\(p, q), (r, s) => (relationTrans a p r, relationTrans b q s))

||| A typed environment is a nested product, related pointwise.
public export
commonEnvironmentSetoid : Vect n LogicalType -> CommonSetoid
commonEnvironmentSetoid [] = commonUnitSetoid
commonEnvironmentSetoid (a :: ctx) =
  commonProductSetoid (commonTypeSetoid a) (commonEnvironmentSetoid ctx)

||| Lookup is extensional for every typed variable, including arrow variables.
public export
commonEnvironmentLookup : (ctx : Vect n LogicalType) -> (a : LogicalType) ->
  LogicalVar ctx a -> CommonMorphism (commonEnvironmentSetoid ctx) (commonTypeSetoid a)
commonEnvironmentLookup (a :: ctx) a LHere = MkCommonMorphism (\env => fst env) (\rel => fst rel)
commonEnvironmentLookup (b :: ctx) a (LThere v) =
  MkCommonMorphism (\env => applyMorphism (commonEnvironmentLookup ctx a v) (snd env))
    (\rel => respectsRelation (commonEnvironmentLookup ctx a v) (snd rel))

||| Currying preserves both related environments and related arguments.
public export
commonCurry : {env, a, b : CommonSetoid} ->
  CommonMorphism (commonProductSetoid a env) b ->
  CommonMorphism env (commonArrowSetoid a b)
commonCurry body = MkCommonMorphism
  (\e => MkCommonMorphism (\x => applyMorphism body (x, e))
    (\xy => respectsRelation body (xy, relationRefl env e)))
  (\ee, x, y, xy => respectsRelation body (xy, ee))

||| Application is extensional in both its function and argument.
public export
commonApply : {env, a, b : CommonSetoid} ->
  CommonMorphism env (commonArrowSetoid a b) -> CommonMorphism env a ->
  CommonMorphism env b
commonApply f x = MkCommonMorphism
  (\e => applyMorphism (applyMorphism f e) (applyMorphism x e))
  (\ee => commonApplicationCongruence (respectsRelation f ee) (respectsRelation x ee))

public export
commonConstant : {env, a : CommonSetoid} -> carrier a -> CommonMorphism env a
commonConstant value = MkCommonMorphism (\_ => value) (\_ => relationRefl a value)

||| An explicit runtime witness for one erased common typing derivation.
public export
data HigherOrderTerm : (ctx : Vect n LogicalType) -> (a : LogicalType) ->
  {0 t : CommonTerm n} -> (0 typing : CommonHasType ctx t a) -> Type where
  HOVar : (ctx : Vect n LogicalType) -> (a : LogicalType) ->
    (v : LogicalVar ctx a) -> HigherOrderTerm ctx a (CVariable v)
  HOUnit : (ctx : Vect n LogicalType) -> HigherOrderTerm ctx LUnit CUnitType
  HOBool : (ctx : Vect n LogicalType) -> (b : Bool) -> HigherOrderTerm ctx LBool (CBoolType {b})
  HOLambda : (ctx : Vect n LogicalType) -> (a, b : LogicalType) ->
    {0 body : CommonHasType (a :: ctx) tm b} -> HigherOrderTerm (a :: ctx) b body ->
    HigherOrderTerm ctx (LArrow a b) (CLambdaType body)
  HOApplication : (ctx : Vect n LogicalType) -> (a, b : LogicalType) ->
    {0 f : CommonHasType ctx ft (LArrow a b)} -> {0 x : CommonHasType ctx xt a} ->
    HigherOrderTerm ctx (LArrow a b) f -> HigherOrderTerm ctx a x ->
    HigherOrderTerm ctx b (CApplicationType f x)
  HOUnitElim : (ctx : Vect n LogicalType) -> (a : LogicalType) ->
    {0 x : CommonHasType ctx xt LUnit} -> {0 body : CommonHasType ctx bt a} ->
    HigherOrderTerm ctx LUnit x -> HigherOrderTerm ctx a body ->
    HigherOrderTerm ctx a (CUnitEliminationType x body)
  HOIf : (ctx : Vect n LogicalType) -> (a : LogicalType) ->
    {0 c : CommonHasType ctx ct LBool} -> {0 t : CommonHasType ctx tt a} -> {0 f : CommonHasType ctx ft a} ->
    HigherOrderTerm ctx LBool c -> HigherOrderTerm ctx a t -> HigherOrderTerm ctx a f ->
    HigherOrderTerm ctx a (CConditionalType c t f)

public export
commonChoose : Bool -> a -> a -> a
commonChoose False t f = f
commonChoose True t f = t

public export
commonIf : {env, a : CommonSetoid} -> CommonMorphism env Fibril.Cubical.Logical.ShadowCommon.commonBoolSetoid ->
  CommonMorphism env a -> CommonMorphism env a -> CommonMorphism env a
commonIf c t f = MkCommonMorphism
  (\e => commonChoose (applyMorphism c e) (applyMorphism t e) (applyMorphism f e))
  (\{x}, {y}, xy => choose (applyMorphism c x) (applyMorphism c y) (respectsRelation c xy) {x} {y} xy)
  where
    choose : (b1, b2 : Bool) -> b1 = b2 -> {x, y : carrier env} -> related env x y ->
      related a (commonChoose b1 (applyMorphism t x) (applyMorphism f x))
                (commonChoose b2 (applyMorphism t y) (applyMorphism f y))
    choose False False Refl xy = respectsRelation f xy
    choose True True Refl xy = respectsRelation t xy

public export
commonUnitElimination : {env, a : CommonSetoid} -> CommonMorphism env Fibril.Cubical.Logical.ShadowCommon.commonUnitSetoid ->
  CommonMorphism env a -> CommonMorphism env a
commonUnitElimination x body = body

public export
higherOrderTermSemantics : {ctx : Vect n LogicalType} -> {a : LogicalType} ->
  {0 typing : CommonHasType ctx t a} -> HigherOrderTerm ctx a typing ->
  CommonMorphism (commonEnvironmentSetoid ctx) (commonTypeSetoid a)
higherOrderTermSemantics (HOVar ctx a v) = commonEnvironmentLookup ctx a v
higherOrderTermSemantics (HOUnit ctx) = commonConstant ()
higherOrderTermSemantics (HOBool ctx b) = commonConstant b
higherOrderTermSemantics (HOLambda ctx a b body) = commonCurry (higherOrderTermSemantics body)
higherOrderTermSemantics (HOApplication ctx a b f x) = commonApply (higherOrderTermSemantics f) (higherOrderTermSemantics x)
higherOrderTermSemantics (HOUnitElim ctx a x body) = commonUnitElimination (higherOrderTermSemantics x) (higherOrderTermSemantics body)
higherOrderTermSemantics (HOIf ctx a c t f) = commonIf (higherOrderTermSemantics c) (higherOrderTermSemantics t) (higherOrderTermSemantics f)

||| Interpretation of an application computes to semantic application.
||| Splitting the result type exposes the interpreter’s dependent case tree.
public export
higherOrderApplicationBeta : {ctx : Vect n LogicalType} -> {a, b : LogicalType} ->
  {0 ft : CommonHasType ctx tmf (LArrow a b)} ->
  {0 xt : CommonHasType ctx tmx a} ->
  (f : HigherOrderTerm ctx (LArrow a b) ft) ->
  (arg : HigherOrderTerm ctx a xt) ->
  higherOrderTermSemantics (HOApplication ctx a b f arg) =
    commonApply (higherOrderTermSemantics f) (higherOrderTermSemantics arg)
higherOrderApplicationBeta {b = LUnit} f arg = Refl
higherOrderApplicationBeta {b = LBool} f arg = Refl
higherOrderApplicationBeta {b = LArrow c d} f arg = Refl


||| Pointwise form of the application beta law.
public export
higherOrderApplicationBetaAt : {ctx : Vect n LogicalType} -> {a, b : LogicalType} ->
  {0 ft : CommonHasType ctx tmf (LArrow a b)} ->
  {0 xt : CommonHasType ctx tmx a} ->
  (f : HigherOrderTerm ctx (LArrow a b) ft) ->
  (arg : HigherOrderTerm ctx a xt) -> (env : carrier (commonEnvironmentSetoid ctx)) ->
  applyMorphism (higherOrderTermSemantics (HOApplication ctx a b f arg)) env =
    applyMorphism (applyMorphism (higherOrderTermSemantics f) env)
      (applyMorphism (higherOrderTermSemantics arg) env)
higherOrderApplicationBetaAt f arg env =
  cong (\m => applyMorphism m env) (higherOrderApplicationBeta f arg)

||| Structural alignment retains the same intermediate type at every application.
||| It relates actual witnesses, not semantic values or arbitrary typings.
public export
data HigherOrderAlignment : {ctx : Vect n LogicalType} -> {a : LogicalType} ->
  {0 t : CommonTerm n} -> {0 leftTy, rightTy : CommonHasType ctx t a} ->
  HigherOrderTerm ctx a leftTy -> HigherOrderTerm ctx a rightTy -> Type where
  AlignVar : (ctx : Vect n LogicalType) -> (a : LogicalType) -> (v : LogicalVar ctx a) ->
    HigherOrderAlignment (HOVar ctx a v) (HOVar ctx a v)
  AlignUnit : (ctx : Vect n LogicalType) -> HigherOrderAlignment (HOUnit ctx) (HOUnit ctx)
  AlignBool : (ctx : Vect n LogicalType) -> (b : Bool) -> HigherOrderAlignment (HOBool ctx b) (HOBool ctx b)
  AlignLambda : {0 lt, rt : CommonHasType (a :: ctx) tm b} ->
    {left : HigherOrderTerm (a :: ctx) b lt} -> {right : HigherOrderTerm (a :: ctx) b rt} ->
    HigherOrderAlignment left right ->
    HigherOrderAlignment (HOLambda ctx a b left) (HOLambda ctx a b right)
  AlignApplication : {0 lf, rf : CommonHasType ctx ft (LArrow a b)} ->
    {0 lx, rx : CommonHasType ctx xt a} ->
    {leftF : HigherOrderTerm ctx (LArrow a b) lf} -> {rightF : HigherOrderTerm ctx (LArrow a b) rf} ->
    {leftX : HigherOrderTerm ctx a lx} -> {rightX : HigherOrderTerm ctx a rx} ->
    HigherOrderAlignment leftF rightF -> HigherOrderAlignment leftX rightX ->
    HigherOrderAlignment (HOApplication ctx a b leftF leftX) (HOApplication ctx a b rightF rightX)
  AlignUnitElim : {0 lx, rx : CommonHasType ctx xt LUnit} -> {0 lb, rb : CommonHasType ctx bt a} ->
    {leftX : HigherOrderTerm ctx LUnit lx} -> {rightX : HigherOrderTerm ctx LUnit rx} ->
    {leftB : HigherOrderTerm ctx a lb} -> {rightB : HigherOrderTerm ctx a rb} ->
    HigherOrderAlignment leftX rightX -> HigherOrderAlignment leftB rightB ->
    HigherOrderAlignment (HOUnitElim ctx a leftX leftB) (HOUnitElim ctx a rightX rightB)
  AlignIf : {0 lc, rc : CommonHasType ctx ct LBool} -> {0 lt, rt : CommonHasType ctx tt a} -> {0 lf, rf : CommonHasType ctx ft a} ->
    {leftC : HigherOrderTerm ctx LBool lc} -> {rightC : HigherOrderTerm ctx LBool rc} ->
    {leftT : HigherOrderTerm ctx a lt} -> {rightT : HigherOrderTerm ctx a rt} ->
    {leftF : HigherOrderTerm ctx a lf} -> {rightF : HigherOrderTerm ctx a rf} ->
    HigherOrderAlignment leftC rightC -> HigherOrderAlignment leftT rightT -> HigherOrderAlignment leftF rightF ->
    HigherOrderAlignment (HOIf ctx a leftC leftT leftF) (HOIf ctx a rightC rightT rightF)

||| Cross-witness application from explicitly related function and argument values.
public export
higherOrderApplicationRelated : {arg, result : LogicalType} ->
  {f, g : CommonMorphism (commonTypeSetoid arg) (commonTypeSetoid result)} ->
  {x, y : carrier (commonTypeSetoid arg)} ->
  related (commonArrowSetoid (commonTypeSetoid arg) (commonTypeSetoid result)) f g ->
  related (commonTypeSetoid arg) x y ->
  related (commonTypeSetoid result) (applyMorphism f x) (applyMorphism g y)
higherOrderApplicationRelated {arg} {result} {f} {g} {x} {y} fg xy =
  commonApplicationCongruence {a = commonTypeSetoid arg} {b = commonTypeSetoid result}
    {f} {g} {x} {y} fg xy

||| Related Boolean choices select related branches at any logical type.
public export
higherOrderChoiceRelated : {a : LogicalType} -> (c, d : Bool) -> c = d ->
  {lt, rt, lf, rf : carrier (commonTypeSetoid a)} ->
  related (commonTypeSetoid a) lt rt -> related (commonTypeSetoid a) lf rf ->
  related (commonTypeSetoid a) (commonChoose c lt lf) (commonChoose d rt rf)
higherOrderChoiceRelated False False Refl tr fr = fr
higherOrderChoiceRelated True True Refl tr fr = tr

||| Aligned variables interpret related environments to related values.
public export
higherOrderAlignedVariableRelated : (ctx : Vect n LogicalType) -> (a : LogicalType) ->
  (v : LogicalVar ctx a) -> (x, y : carrier (commonEnvironmentSetoid ctx)) ->
  related (commonEnvironmentSetoid ctx) x y ->
  related (commonTypeSetoid a) (applyMorphism (higherOrderTermSemantics (HOVar ctx a v)) x)
                              (applyMorphism (higherOrderTermSemantics (HOVar ctx a v)) y)
higherOrderAlignedVariableRelated ctx a v x y xy = respectsRelation (commonEnvironmentLookup ctx a v) xy

||| Aligned witnesses preserve semantic relatedness across related environments.
public export
higherOrderAlignedRelated : {ctx : Vect n LogicalType} -> {a : LogicalType} ->
  {0 lt, rt : CommonHasType ctx t a} ->
  {left : HigherOrderTerm ctx a lt} -> {right : HigherOrderTerm ctx a rt} ->
  HigherOrderAlignment left right -> (x, y : carrier (commonEnvironmentSetoid ctx)) ->
  related (commonEnvironmentSetoid ctx) x y ->
  related (commonTypeSetoid a) (applyMorphism (higherOrderTermSemantics left) x)
    (applyMorphism (higherOrderTermSemantics right) y)
higherOrderAlignedRelated {a = LUnit} (AlignVar ctx _ v) x y xy = higherOrderAlignedVariableRelated ctx LUnit v x y xy
higherOrderAlignedRelated {a = LBool} (AlignVar ctx _ v) x y xy = higherOrderAlignedVariableRelated ctx LBool v x y xy
higherOrderAlignedRelated {a = (LArrow c d)} (AlignVar ctx _ v) x y xy = higherOrderAlignedVariableRelated ctx (LArrow c d) v x y xy
higherOrderAlignedRelated {a = LUnit} (AlignUnit ctx) x y xy = Refl
higherOrderAlignedRelated {a = LBool} (AlignBool ctx b) x y xy = Refl
higherOrderAlignedRelated {a = (LArrow a b)} (AlignLambda body) x y xy =
  \u, v, uv => higherOrderAlignedRelated body (u, x) (v, y) (uv, xy)
higherOrderAlignedRelated {a = LUnit} (AlignApplication {a = domain} {leftF} {rightF} {leftX} {rightX} f arg) x y xy =
  rewrite higherOrderApplicationBetaAt leftF leftX x in
  rewrite higherOrderApplicationBetaAt rightF rightX y in
  higherOrderApplicationRelated {arg = domain} {result = LUnit} (higherOrderAlignedRelated f x y xy) (higherOrderAlignedRelated arg x y xy)
higherOrderAlignedRelated {a = LBool} (AlignApplication {a = domain} {leftF} {rightF} {leftX} {rightX} f arg) x y xy =
  rewrite higherOrderApplicationBetaAt leftF leftX x in
  rewrite higherOrderApplicationBetaAt rightF rightX y in
  higherOrderApplicationRelated {arg = domain} {result = LBool} (higherOrderAlignedRelated f x y xy) (higherOrderAlignedRelated arg x y xy)
higherOrderAlignedRelated {a = (LArrow c d)} (AlignApplication {a = domain} {leftF} {rightF} {leftX} {rightX} f arg) x y xy =
  rewrite higherOrderApplicationBetaAt leftF leftX x in
  rewrite higherOrderApplicationBetaAt rightF rightX y in
  higherOrderApplicationRelated {arg = domain} {result = (LArrow c d)} (higherOrderAlignedRelated f x y xy) (higherOrderAlignedRelated arg x y xy)
higherOrderAlignedRelated {a = LUnit} (AlignUnitElim unit body) x y xy = higherOrderAlignedRelated body x y xy
higherOrderAlignedRelated {a = LBool} (AlignUnitElim unit body) x y xy = higherOrderAlignedRelated body x y xy
higherOrderAlignedRelated {a = (LArrow c d)} (AlignUnitElim unit body) x y xy = higherOrderAlignedRelated body x y xy
higherOrderAlignedRelated {a = LUnit} (AlignIf c t f) x y xy =
  higherOrderChoiceRelated {a = LUnit} _ _ (higherOrderAlignedRelated c x y xy)
    (higherOrderAlignedRelated t x y xy) (higherOrderAlignedRelated f x y xy)
higherOrderAlignedRelated {a = LBool} (AlignIf c t f) x y xy =
  higherOrderChoiceRelated {a = LBool} _ _ (higherOrderAlignedRelated c x y xy)
    (higherOrderAlignedRelated t x y xy) (higherOrderAlignedRelated f x y xy)
higherOrderAlignedRelated {a = (LArrow cty dty)} (AlignIf c t f) x y xy =
  higherOrderChoiceRelated {a = (LArrow cty dty)} _ _ (higherOrderAlignedRelated c x y xy)
    (higherOrderAlignedRelated t x y xy) (higherOrderAlignedRelated f x y xy)

||| Dimensions use equality, not a Boolean approximation of the four-pair model.
public export
commonDMSetoid : CommonSetoid
commonDMSetoid = MkCommonSetoid DM (\x, y => x = y) (\x => Refl) (\p => sym p) (\p, q => trans p q)

||| Named paths are independent values, retained unchanged under ordinary binders.
public export
commonPathEnvironmentSetoid : Vect k LogicalType -> CommonSetoid
commonPathEnvironmentSetoid [] = commonUnitSetoid
commonPathEnvironmentSetoid (a :: paths) = commonProductSetoid
  (commonArrowSetoid commonDMSetoid (commonTypeSetoid a)) (commonPathEnvironmentSetoid paths)

public export
commonPathEnvironmentLookup : (paths : Vect k LogicalType) -> (a : LogicalType) ->
  LogicalVar paths a -> CommonMorphism (commonPathEnvironmentSetoid paths) (commonArrowSetoid Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid (commonTypeSetoid a))
commonPathEnvironmentLookup (a :: paths) a LHere = MkCommonMorphism fst fst
commonPathEnvironmentLookup (b :: paths) a (LThere v) = MkCommonMorphism
  (\env => applyMorphism (commonPathEnvironmentLookup paths a v) (snd env))
  (\rel => respectsRelation (commonPathEnvironmentLookup paths a v) (snd rel))

||| Runtime evidence for the particular erased path typing derivation.
public export
data HigherOrderPathTerm : (ctx : Vect n LogicalType) -> (paths : Vect k LogicalType) ->
  (a : LogicalType) -> (d : Nat) -> {0 t : CommonPathTerm n k d} ->
  (0 typing : CommonPathHasType ctx paths t a) -> Type where
  HOPOrdinary : (ctx : Vect n LogicalType) -> (paths : Vect k LogicalType) -> (a : LogicalType) -> (d : Nat) ->
    {0 ty : CommonHasType ctx t a} -> HigherOrderTerm ctx a ty -> HigherOrderPathTerm ctx paths a d (CPOrdinaryType ty)
  HOPAt : (ctx : Vect n LogicalType) -> (paths : Vect k LogicalType) -> (a : LogicalType) -> (d : Nat) ->
    (p : LogicalVar paths a) -> (i : ScopedInterval d) -> HigherOrderPathTerm ctx paths a d (CPAtType {i} p)
  HOPLambda : (ctx : Vect n LogicalType) -> (paths : Vect k LogicalType) -> (a, b : LogicalType) -> (d : Nat) ->
    {0 t : CommonPathTerm (S n) k d} -> {0 body : CommonPathHasType (a :: ctx) paths t b} -> HigherOrderPathTerm (a :: ctx) paths b d body ->
    HigherOrderPathTerm ctx paths (LArrow a b) d (CPLamType body)
  HOPApplication : (ctx : Vect n LogicalType) -> (paths : Vect k LogicalType) -> (a, b : LogicalType) -> (d : Nat) ->
    {0 ft, xt : CommonPathTerm n k d} -> {0 f : CommonPathHasType ctx paths ft (LArrow a b)} -> {0 x : CommonPathHasType ctx paths xt a} ->
    HigherOrderPathTerm ctx paths (LArrow a b) d f -> HigherOrderPathTerm ctx paths a d x ->
    HigherOrderPathTerm ctx paths b d (CPAppType f x)
  HOPUnitElim : (ctx : Vect n LogicalType) -> (paths : Vect k LogicalType) -> (a : LogicalType) -> (d : Nat) ->
    {0 xt, bt : CommonPathTerm n k d} -> {0 x : CommonPathHasType ctx paths xt LUnit} -> {0 b : CommonPathHasType ctx paths bt a} ->
    HigherOrderPathTerm ctx paths LUnit d x -> HigherOrderPathTerm ctx paths a d b ->
    HigherOrderPathTerm ctx paths a d (CPUnitElimType x b)
  HOPIf : (ctx : Vect n LogicalType) -> (paths : Vect k LogicalType) -> (a : LogicalType) -> (d : Nat) ->
    {0 ct, tt, ft : CommonPathTerm n k d} -> {0 c : CommonPathHasType ctx paths ct LBool} -> {0 t : CommonPathHasType ctx paths tt a} -> {0 f : CommonPathHasType ctx paths ft a} ->
    HigherOrderPathTerm ctx paths LBool d c -> HigherOrderPathTerm ctx paths a d t -> HigherOrderPathTerm ctx paths a d f ->
    HigherOrderPathTerm ctx paths a d (CPIfType c t f)

||| Interpret in the product of the ordinary and independent named-path environments.
public export
higherOrderPathSemantics : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} -> {a : LogicalType} -> {d : Nat} ->
  {0 t : CommonPathTerm n k d} -> {0 typing : CommonPathHasType ctx paths t a} -> HigherOrderPathTerm ctx paths a d typing -> (Fin d -> DM) ->
  CommonMorphism (commonProductSetoid (commonEnvironmentSetoid ctx) (commonPathEnvironmentSetoid paths)) (commonTypeSetoid a)
higherOrderPathSemantics (HOPOrdinary ctx paths a d w) valuation = MkCommonMorphism
  (\env => applyMorphism (higherOrderTermSemantics w) (fst env))
  (\rel => respectsRelation (higherOrderTermSemantics w) (fst rel))
higherOrderPathSemantics (HOPAt ctx paths a d p i) valuation = MkCommonMorphism
  (\env => applyMorphism (applyMorphism (commonPathEnvironmentLookup paths a p) (snd env)) (evalDMVal valuation i))
  (\rel => respectsRelation (commonPathEnvironmentLookup paths a p) (snd rel) _ _ Refl)
higherOrderPathSemantics (HOPLambda ctx paths a b d body) valuation = commonCurry $ MkCommonMorphism
  (\env => applyMorphism (higherOrderPathSemantics body valuation) ((fst env, fst (snd env)), snd (snd env)))
  (\{x}, {y}, rel => respectsRelation (higherOrderPathSemantics body valuation) {x = ((fst x, fst (snd x)), snd (snd x))} {y = ((fst y, fst (snd y)), snd (snd y))} ((fst rel, fst (snd rel)), snd (snd rel)))
higherOrderPathSemantics (HOPApplication ctx paths a b d f x) valuation =
  commonApply (higherOrderPathSemantics f valuation) (higherOrderPathSemantics x valuation)
higherOrderPathSemantics (HOPUnitElim ctx paths a d x b) valuation =
  commonUnitElimination (higherOrderPathSemantics x valuation) (higherOrderPathSemantics b valuation)
higherOrderPathSemantics (HOPIf ctx paths a d c t f) valuation =
  commonIf (higherOrderPathSemantics c valuation) (higherOrderPathSemantics t valuation) (higherOrderPathSemantics f valuation)

||| Independent named paths must match each declared endpoint in every ordinary
||| environment. Variable-dependent endpoints can therefore make this empty.
public export
data HigherOrderAdmissible : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
  (0 decls : CommonDeclarations ctx paths) -> carrier (commonPathEnvironmentSetoid paths) -> Type where
  HOAdmissibleNil : HigherOrderAdmissible CommonNoPaths ()
  HOAdmissibleCons : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
    {0 rest : CommonDeclarations ctx paths} -> {ps : carrier (commonPathEnvironmentSetoid paths)} ->
    {0 lt : CommonHasType ctx l a} -> {0 rt : CommonHasType ctx r a} ->
    (left : HigherOrderTerm ctx a lt) -> (right : HigherOrderTerm ctx a rt) ->
    {path : CommonMorphism Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid (commonTypeSetoid a)} ->
    ((env : carrier (commonEnvironmentSetoid ctx)) -> related (commonTypeSetoid a)
      (applyMorphism path (False, False)) (applyMorphism (higherOrderTermSemantics left) env)) ->
    ((env : carrier (commonEnvironmentSetoid ctx)) -> related (commonTypeSetoid a)
      (applyMorphism path (True, True)) (applyMorphism (higherOrderTermSemantics right) env)) ->
    HigherOrderAdmissible rest ps ->
    HigherOrderAdmissible (CommonDeclarePath l r lt rt rest) (path, ps)

public export
data HigherOrderEndpoints : (ctx : Vect n LogicalType) -> {paths : Vect k LogicalType} ->
  (p : LogicalVar paths a) -> (l, r : CommonTerm n) ->
  (ps : carrier (commonPathEnvironmentSetoid paths)) -> Type where
  HOEndpoints : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
    {p : LogicalVar paths a} -> {ps : carrier (commonPathEnvironmentSetoid paths)} ->
    {0 lt : CommonHasType ctx l a} -> {0 rt : CommonHasType ctx r a} ->
    (left : HigherOrderTerm ctx a lt) -> (right : HigherOrderTerm ctx a rt) ->
    ((env : carrier (commonEnvironmentSetoid ctx)) -> related (commonTypeSetoid a)
      (applyMorphism (applyMorphism (commonPathEnvironmentLookup paths a p) ps) (False, False))
      (applyMorphism (higherOrderTermSemantics left) env)) ->
    ((env : carrier (commonEnvironmentSetoid ctx)) -> related (commonTypeSetoid a)
      (applyMorphism (applyMorphism (commonPathEnvironmentLookup paths a p) ps) (True, True))
      (applyMorphism (higherOrderTermSemantics right) env)) ->
    HigherOrderEndpoints ctx p l r ps

public export
higherOrderDeclaredLookup : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
  {0 decls : CommonDeclarations ctx paths} -> {p : LogicalVar paths a} -> {l, r : CommonTerm n} ->
  CommonDeclaredPath decls p l r -> (ps : carrier (commonPathEnvironmentSetoid paths)) ->
  HigherOrderAdmissible decls ps -> HigherOrderEndpoints ctx p l r ps
higherOrderDeclaredLookup CommonDeclaredHere (path, ps) (HOAdmissibleCons left right zero one rest) =
  HOEndpoints left right zero one
higherOrderDeclaredLookup {ctx} {l} {r} {p = LThere p} (CommonDeclaredThere declared) (path, ps) (HOAdmissibleCons left right zero one rest) =
  case higherOrderDeclaredLookup {ctx} {l} {r} {p} declared ps rest of
    HOEndpoints left right z o => HOEndpoints {ctx} {l} {r} {p = LThere p} left right z o

||| The selected endpoint witness remains indexed by the declared syntax.
public export
data HigherOrderEndpointAtFace : (ctx : Vect n LogicalType) -> {paths : Vect k LogicalType} ->
  (p : LogicalVar paths a) -> (term : CommonTerm n) ->
  (ps : carrier (commonPathEnvironmentSetoid paths)) ->
  (env : carrier (commonEnvironmentSetoid ctx)) -> (value : DM) -> Type where
  HOEndpointAtFace : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
    {p : LogicalVar paths a} -> {ps : carrier (commonPathEnvironmentSetoid paths)} ->
    {env : carrier (commonEnvironmentSetoid ctx)} -> {value : DM} ->
    {0 ty : CommonHasType ctx term a} -> (w : HigherOrderTerm ctx a ty) ->
    related (commonTypeSetoid a)
      (applyMorphism (applyMorphism (commonPathEnvironmentLookup paths a p) ps) value)
      (applyMorphism (higherOrderTermSemantics w) env) ->
    HigherOrderEndpointAtFace ctx p term ps env value

public export
higherOrderDeclaredLeftAtFace : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
  {0 decls : CommonDeclarations ctx paths} -> {p : LogicalVar paths a} -> {l, r : CommonTerm n} ->
  CommonDeclaredPath decls p l r -> (ps : carrier (commonPathEnvironmentSetoid paths)) ->
  HigherOrderAdmissible decls ps -> (env : carrier (commonEnvironmentSetoid ctx)) ->
  (valuation : Fin d -> DM) -> (face : ScopedFace d) -> (i : ScopedInterval d) ->
  boundedEndpointEntails face i False = True -> faceAtVal valuation face = True ->
  HigherOrderEndpointAtFace ctx p l ps env (evalDMVal valuation i)
higherOrderDeclaredLeftAtFace declared ps admissible env valuation face i accepted holds =
  case higherOrderDeclaredLookup declared ps admissible of
    HOEndpoints left right zero one =>
      HOEndpointAtFace left (rewrite commonBoundedEndpointValSound valuation face i False accepted holds in zero env)

public export
higherOrderDeclaredRightAtFace : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
  {0 decls : CommonDeclarations ctx paths} -> {p : LogicalVar paths a} -> {l, r : CommonTerm n} ->
  CommonDeclaredPath decls p l r -> (ps : carrier (commonPathEnvironmentSetoid paths)) ->
  HigherOrderAdmissible decls ps -> (env : carrier (commonEnvironmentSetoid ctx)) ->
  (valuation : Fin d -> DM) -> (face : ScopedFace d) -> (i : ScopedInterval d) ->
  boundedEndpointEntails face i True = True -> faceAtVal valuation face = True ->
  HigherOrderEndpointAtFace ctx p r ps env (evalDMVal valuation i)
higherOrderDeclaredRightAtFace declared ps admissible env valuation face i accepted holds =
  case higherOrderDeclaredLookup declared ps admissible of
    HOEndpoints left right zero one =>
      HOEndpointAtFace right (rewrite commonBoundedEndpointValSound valuation face i True accepted holds in one env)

||| Named paths indexed by the ordinary environment, extensionally related.
public export
commonDependentPathEnvironmentSetoid : Vect n LogicalType -> Vect k LogicalType -> CommonSetoid
commonDependentPathEnvironmentSetoid ctx [] = commonUnitSetoid
commonDependentPathEnvironmentSetoid ctx (a :: paths) = commonProductSetoid
  (commonArrowSetoid (commonProductSetoid (commonEnvironmentSetoid ctx) Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid) (commonTypeSetoid a))
  (commonDependentPathEnvironmentSetoid ctx paths)

public export
commonDependentPathLookup : (ctx : Vect n LogicalType) -> (paths : Vect k LogicalType) -> (a : LogicalType) ->
  LogicalVar paths a -> CommonMorphism (commonDependentPathEnvironmentSetoid ctx paths)
    (commonArrowSetoid (commonProductSetoid (commonEnvironmentSetoid ctx) Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid) (commonTypeSetoid a))
commonDependentPathLookup ctx (a :: paths) a LHere = MkCommonMorphism fst fst
commonDependentPathLookup ctx (b :: paths) a (LThere v) = MkCommonMorphism
  (\env => applyMorphism (commonDependentPathLookup ctx paths a v) (snd env))
  (\rel => respectsRelation (commonDependentPathLookup ctx paths a v) (snd rel))

||| Pull back along the projection which discards the freshly bound variable.
public export
weakenDependentPaths : (ctx : Vect n LogicalType) -> (paths : Vect k LogicalType) -> (a : LogicalType) ->
  CommonMorphism (commonDependentPathEnvironmentSetoid ctx paths) (commonDependentPathEnvironmentSetoid (a :: ctx) paths)
weakenDependentPaths ctx [] a = commonConstant ()
weakenDependentPaths ctx (b :: paths) a = MkCommonMorphism
  (\ps => (MkCommonMorphism (\input => applyMorphism (fst ps) (snd (fst input), snd input))
    (\{x}, {y}, rel => respectsRelation (fst ps) {x = (snd (fst x), snd x)} {y = (snd (fst y), snd y)} (snd (fst rel), snd rel)),
    applyMorphism (weakenDependentPaths ctx paths a) (snd ps)))
  (\rel => ((\x, y, xy => fst rel (snd (fst x), snd x) (snd (fst y), snd y) (snd (fst xy), snd xy)),
    respectsRelation (weakenDependentPaths ctx paths a) (snd rel)))

public export
dependentPathSemantics : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} -> {a : LogicalType} -> {d : Nat} ->
  {0 t : CommonPathTerm n k d} -> {0 typing : CommonPathHasType ctx paths t a} -> HigherOrderPathTerm ctx paths a d typing -> (Fin d -> DM) ->
  CommonMorphism (commonProductSetoid (commonEnvironmentSetoid ctx) (commonDependentPathEnvironmentSetoid ctx paths)) (commonTypeSetoid a)
dependentPathSemantics (HOPOrdinary ctx paths a d w) valuation = MkCommonMorphism
  (\env => applyMorphism (higherOrderTermSemantics w) (fst env))
  (\rel => respectsRelation (higherOrderTermSemantics w) (fst rel))
dependentPathSemantics (HOPAt ctx paths a d p i) valuation = MkCommonMorphism
  (\env => applyMorphism (applyMorphism (commonDependentPathLookup ctx paths a p) (snd env)) (fst env, evalDMVal valuation i))
  (\{x}, {y}, rel => respectsRelation (commonDependentPathLookup ctx paths a p) (snd rel) (fst x, evalDMVal valuation i) (fst y, evalDMVal valuation i) (fst rel, Refl))
dependentPathSemantics (HOPLambda ctx paths a b d body) valuation = commonCurry $ MkCommonMorphism
  (\env => applyMorphism (dependentPathSemantics body valuation) ((fst env, fst (snd env)), applyMorphism (weakenDependentPaths ctx paths a) (snd (snd env))))
  (\{x}, {y}, rel => respectsRelation (dependentPathSemantics body valuation) {x = ((fst x, fst (snd x)), applyMorphism (weakenDependentPaths ctx paths a) (snd (snd x)))} {y = ((fst y, fst (snd y)), applyMorphism (weakenDependentPaths ctx paths a) (snd (snd y)))} ((fst rel, fst (snd rel)), respectsRelation (weakenDependentPaths ctx paths a) (snd (snd rel))))
dependentPathSemantics (HOPApplication ctx paths a b d f x) valuation = commonApply (dependentPathSemantics f valuation) (dependentPathSemantics x valuation)
dependentPathSemantics (HOPUnitElim ctx paths a d x b) valuation = commonUnitElimination (dependentPathSemantics x valuation) (dependentPathSemantics b valuation)
dependentPathSemantics (HOPIf ctx paths a d c t f) valuation = commonIf (dependentPathSemantics c valuation) (dependentPathSemantics t valuation) (dependentPathSemantics f valuation)

||| Structural alignment of actual dependent-path witnesses.
public export
data HigherOrderPathAlignment : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
  {a : LogicalType} -> {d : Nat} -> {0 t : CommonPathTerm n k d} ->
  {0 lt, rt : CommonPathHasType ctx paths t a} ->
  HigherOrderPathTerm ctx paths a d lt -> HigherOrderPathTerm ctx paths a d rt -> Type where
  AlignPathOrdinary : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} -> {d : Nat} -> {a : LogicalType} ->
    {0 lt, rt : CommonHasType ctx tm a} ->
    {left : HigherOrderTerm ctx a lt} -> {right : HigherOrderTerm ctx a rt} ->
    HigherOrderAlignment left right ->
    HigherOrderPathAlignment (HOPOrdinary ctx paths a d left) (HOPOrdinary ctx paths a d right)
  AlignPathAt : (ctx : Vect n LogicalType) -> (paths : Vect k LogicalType) -> (a : LogicalType) ->
    (d : Nat) -> (p : LogicalVar paths a) -> (i : ScopedInterval d) ->
    HigherOrderPathAlignment (HOPAt ctx paths a d p i) (HOPAt ctx paths a d p i)
  AlignPathLambda : {0 lt, rt : CommonPathHasType (a :: ctx) paths tm b} ->
    {left : HigherOrderPathTerm (a :: ctx) paths b d lt} -> {right : HigherOrderPathTerm (a :: ctx) paths b d rt} ->
    HigherOrderPathAlignment left right ->
    HigherOrderPathAlignment (HOPLambda ctx paths a b d left) (HOPLambda ctx paths a b d right)
  AlignPathApplication : {0 lf, rf : CommonPathHasType ctx paths ft (LArrow a b)} ->
    {0 lx, rx : CommonPathHasType ctx paths xt a} ->
    {leftF : HigherOrderPathTerm ctx paths (LArrow a b) d lf} -> {rightF : HigherOrderPathTerm ctx paths (LArrow a b) d rf} ->
    {leftX : HigherOrderPathTerm ctx paths a d lx} -> {rightX : HigherOrderPathTerm ctx paths a d rx} ->
    HigherOrderPathAlignment leftF rightF -> HigherOrderPathAlignment leftX rightX ->
    HigherOrderPathAlignment (HOPApplication ctx paths a b d leftF leftX) (HOPApplication ctx paths a b d rightF rightX)
  AlignPathUnitElim : {0 lx, rx : CommonPathHasType ctx paths xt LUnit} -> {0 lb, rb : CommonPathHasType ctx paths bt a} ->
    {leftX : HigherOrderPathTerm ctx paths LUnit d lx} -> {rightX : HigherOrderPathTerm ctx paths LUnit d rx} ->
    {leftB : HigherOrderPathTerm ctx paths a d lb} -> {rightB : HigherOrderPathTerm ctx paths a d rb} ->
    HigherOrderPathAlignment leftX rightX -> HigherOrderPathAlignment leftB rightB ->
    HigherOrderPathAlignment (HOPUnitElim ctx paths a d leftX leftB) (HOPUnitElim ctx paths a d rightX rightB)
  AlignPathIf : {0 lc, rc : CommonPathHasType ctx paths ct LBool} -> {0 lt, rt : CommonPathHasType ctx paths tt a} -> {0 lf, rf : CommonPathHasType ctx paths ft a} ->
    {leftC : HigherOrderPathTerm ctx paths LBool d lc} -> {rightC : HigherOrderPathTerm ctx paths LBool d rc} ->
    {leftT : HigherOrderPathTerm ctx paths a d lt} -> {rightT : HigherOrderPathTerm ctx paths a d rt} ->
    {leftF : HigherOrderPathTerm ctx paths a d lf} -> {rightF : HigherOrderPathTerm ctx paths a d rf} ->
    HigherOrderPathAlignment leftC rightC -> HigherOrderPathAlignment leftT rightT -> HigherOrderPathAlignment leftF rightF ->
    HigherOrderPathAlignment (HOPIf ctx paths a d leftC leftT leftF) (HOPIf ctx paths a d rightC rightT rightF)

||| Application interpretation reduces pointwise for every result type.
public export
dependentPathApplicationBeta : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
  {a, b : LogicalType} -> {d : Nat} -> {0 f, x : CommonPathTerm n k d} ->
  {0 ft : CommonPathHasType ctx paths f (LArrow a b)} -> {0 xt : CommonPathHasType ctx paths x a} ->
  (fn : HigherOrderPathTerm ctx paths (LArrow a b) d ft) -> (arg : HigherOrderPathTerm ctx paths a d xt) ->
  (valuation : Fin d -> DM) -> (env : carrier (commonProductSetoid (commonEnvironmentSetoid ctx) (commonDependentPathEnvironmentSetoid ctx paths))) ->
  applyMorphism (dependentPathSemantics (HOPApplication ctx paths a b d fn arg) valuation) env =
  applyMorphism (applyMorphism (dependentPathSemantics fn valuation) env) (applyMorphism (dependentPathSemantics arg valuation) env)
dependentPathApplicationBeta {b = LUnit} fn arg valuation env = Refl
dependentPathApplicationBeta {b = LBool} fn arg valuation env = Refl
dependentPathApplicationBeta {b = LArrow c d} fn arg valuation env = Refl

public export
dependentPathAlignedRelated : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} -> {a : LogicalType} -> {d : Nat} -> {0 t : CommonPathTerm n k d} ->
  {0 lt, rt : CommonPathHasType ctx paths t a} ->
  {left : HigherOrderPathTerm ctx paths a d lt} -> {right : HigherOrderPathTerm ctx paths a d rt} ->
  HigherOrderPathAlignment left right -> (valuation : Fin d -> DM) ->
  (x, y : carrier (commonProductSetoid (commonEnvironmentSetoid ctx) (commonDependentPathEnvironmentSetoid ctx paths))) ->
  related (commonProductSetoid (commonEnvironmentSetoid ctx) (commonDependentPathEnvironmentSetoid ctx paths)) x y ->
  related (commonTypeSetoid a) (applyMorphism (dependentPathSemantics left valuation) x)
    (applyMorphism (dependentPathSemantics right valuation) y)
dependentPathAlignedRelated {a = LUnit} (AlignPathOrdinary align) valuation x y xy = higherOrderAlignedRelated align (fst x) (fst y) (fst xy)
dependentPathAlignedRelated {a = LUnit} (AlignPathAt ctx paths _ d p i) valuation x y xy =
  respectsRelation (commonDependentPathLookup ctx paths LUnit p) (snd xy) (fst x, evalDMVal valuation i) (fst y, evalDMVal valuation i) (fst xy, Refl)
dependentPathAlignedRelated {a = LBool} (AlignPathOrdinary align) valuation x y xy = higherOrderAlignedRelated align (fst x) (fst y) (fst xy)
dependentPathAlignedRelated {a = LBool} (AlignPathAt ctx paths _ d p i) valuation x y xy =
  respectsRelation (commonDependentPathLookup ctx paths LBool p) (snd xy) (fst x, evalDMVal valuation i) (fst y, evalDMVal valuation i) (fst xy, Refl)
dependentPathAlignedRelated {a = (LArrow c dty)} (AlignPathOrdinary align) valuation x y xy = higherOrderAlignedRelated align (fst x) (fst y) (fst xy)
dependentPathAlignedRelated {a = (LArrow c dty)} (AlignPathAt ctx paths _ d p i) valuation x y xy =
  respectsRelation (commonDependentPathLookup ctx paths (LArrow c dty) p) (snd xy) (fst x, evalDMVal valuation i) (fst y, evalDMVal valuation i) (fst xy, Refl)
dependentPathAlignedRelated {a = (LArrow domain result)} (AlignPathLambda {ctx} {paths} body) valuation x y xy =
  \u, v, uv => dependentPathAlignedRelated body valuation
    ((u, fst x), applyMorphism (weakenDependentPaths ctx paths domain) (snd x))
    ((v, fst y), applyMorphism (weakenDependentPaths ctx paths domain) (snd y))
    ((uv, fst xy), respectsRelation (weakenDependentPaths ctx paths domain) (snd xy))
dependentPathAlignedRelated {a = LUnit} (AlignPathApplication {a = domain} {leftF} {rightF} {leftX} {rightX} f arg) valuation x y xy =
  rewrite dependentPathApplicationBeta leftF leftX valuation x in
  rewrite dependentPathApplicationBeta rightF rightX valuation y in
  higherOrderApplicationRelated {arg = domain} {result = LUnit} (dependentPathAlignedRelated f valuation x y xy) (dependentPathAlignedRelated arg valuation x y xy)
dependentPathAlignedRelated {a = LUnit} (AlignPathUnitElim unit body) valuation x y xy = dependentPathAlignedRelated body valuation x y xy
dependentPathAlignedRelated {a = LUnit} (AlignPathIf cond yes no) valuation x y xy =
  higherOrderChoiceRelated {a = LUnit} _ _ (dependentPathAlignedRelated cond valuation x y xy)
    (dependentPathAlignedRelated yes valuation x y xy) (dependentPathAlignedRelated no valuation x y xy)
dependentPathAlignedRelated {a = LBool} (AlignPathApplication {a = domain} {leftF} {rightF} {leftX} {rightX} f arg) valuation x y xy =
  rewrite dependentPathApplicationBeta leftF leftX valuation x in
  rewrite dependentPathApplicationBeta rightF rightX valuation y in
  higherOrderApplicationRelated {arg = domain} {result = LBool} (dependentPathAlignedRelated f valuation x y xy) (dependentPathAlignedRelated arg valuation x y xy)
dependentPathAlignedRelated {a = LBool} (AlignPathUnitElim unit body) valuation x y xy = dependentPathAlignedRelated body valuation x y xy
dependentPathAlignedRelated {a = LBool} (AlignPathIf cond yes no) valuation x y xy =
  higherOrderChoiceRelated {a = LBool} _ _ (dependentPathAlignedRelated cond valuation x y xy)
    (dependentPathAlignedRelated yes valuation x y xy) (dependentPathAlignedRelated no valuation x y xy)
dependentPathAlignedRelated {a = (LArrow c dty)} (AlignPathApplication {a = domain} {leftF} {rightF} {leftX} {rightX} f arg) valuation x y xy =
  rewrite dependentPathApplicationBeta leftF leftX valuation x in
  rewrite dependentPathApplicationBeta rightF rightX valuation y in
  higherOrderApplicationRelated {arg = domain} {result = (LArrow c dty)} (dependentPathAlignedRelated f valuation x y xy) (dependentPathAlignedRelated arg valuation x y xy)
dependentPathAlignedRelated {a = (LArrow c dty)} (AlignPathUnitElim unit body) valuation x y xy = dependentPathAlignedRelated body valuation x y xy
dependentPathAlignedRelated {a = (LArrow c dty)} (AlignPathIf cond yes no) valuation x y xy =
  higherOrderChoiceRelated {a = (LArrow c dty)} _ _ (dependentPathAlignedRelated cond valuation x y xy)
    (dependentPathAlignedRelated yes valuation x y xy) (dependentPathAlignedRelated no valuation x y xy)

public export
data DependentPathAdmissible : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
  (0 decls : CommonDeclarations ctx paths) -> carrier (commonDependentPathEnvironmentSetoid ctx paths) -> Type where
  DependentAdmissibleNil : DependentPathAdmissible CommonNoPaths ()
  DependentAdmissibleCons : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
    {0 rest : CommonDeclarations ctx paths} -> {ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)} ->
    {0 lt : CommonHasType ctx l a} -> {0 rt : CommonHasType ctx r a} ->
    (left : HigherOrderTerm ctx a lt) -> (right : HigherOrderTerm ctx a rt) ->
    {path : CommonMorphism (commonProductSetoid (commonEnvironmentSetoid ctx) Fibril.Cubical.Logical.ShadowCommon.commonDMSetoid) (commonTypeSetoid a)} ->
    ((env : carrier (commonEnvironmentSetoid ctx)) -> related (commonTypeSetoid a)
      (applyMorphism path (env, (False, False))) (applyMorphism (higherOrderTermSemantics left) env)) ->
    ((env : carrier (commonEnvironmentSetoid ctx)) -> related (commonTypeSetoid a)
      (applyMorphism path (env, (True, True))) (applyMorphism (higherOrderTermSemantics right) env)) ->
    DependentPathAdmissible rest ps ->
    DependentPathAdmissible (CommonDeclarePath l r lt rt rest) (path, ps)

public export
data DependentPathEndpoints : (ctx : Vect n LogicalType) -> {paths : Vect k LogicalType} ->
  (p : LogicalVar paths a) -> (l, r : CommonTerm n) ->
  (ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)) -> Type where
  DependentEndpoints : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
    {p : LogicalVar paths a} -> {ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)} ->
    {0 lt : CommonHasType ctx l a} -> {0 rt : CommonHasType ctx r a} ->
    (left : HigherOrderTerm ctx a lt) -> (right : HigherOrderTerm ctx a rt) ->
    ((env : carrier (commonEnvironmentSetoid ctx)) -> related (commonTypeSetoid a)
      (applyMorphism (applyMorphism (commonDependentPathLookup ctx paths a p) ps) (env, (False, False)))
      (applyMorphism (higherOrderTermSemantics left) env)) ->
    ((env : carrier (commonEnvironmentSetoid ctx)) -> related (commonTypeSetoid a)
      (applyMorphism (applyMorphism (commonDependentPathLookup ctx paths a p) ps) (env, (True, True)))
      (applyMorphism (higherOrderTermSemantics right) env)) ->
    DependentPathEndpoints ctx p l r ps

public export
dependentDeclaredLookup : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
  {0 decls : CommonDeclarations ctx paths} -> {p : LogicalVar paths a} -> {l, r : CommonTerm n} ->
  CommonDeclaredPath decls p l r -> (ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)) ->
  DependentPathAdmissible decls ps -> DependentPathEndpoints ctx p l r ps
dependentDeclaredLookup CommonDeclaredHere (path, ps) (DependentAdmissibleCons left right zero one rest) =
  DependentEndpoints left right zero one
dependentDeclaredLookup {ctx} {l} {r} {p = LThere p} (CommonDeclaredThere declared) (path, ps) (DependentAdmissibleCons left right zero one rest) =
  case dependentDeclaredLookup {ctx} {l} {r} {p} declared ps rest of
    DependentEndpoints left right z o => DependentEndpoints {ctx} {l} {r} {p = LThere p} left right z o

||| The selected endpoint witness remains indexed by the declared syntax.
public export
data DependentEndpointAtFace : (ctx : Vect n LogicalType) -> {paths : Vect k LogicalType} ->
  (p : LogicalVar paths a) -> (term : CommonTerm n) ->
  (ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)) ->
  (env : carrier (commonEnvironmentSetoid ctx)) -> (value : DM) -> Type where
  DependentAtFace : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
    {p : LogicalVar paths a} -> {ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)} ->
    {env : carrier (commonEnvironmentSetoid ctx)} -> {value : DM} ->
    {0 ty : CommonHasType ctx term a} -> (w : HigherOrderTerm ctx a ty) ->
    related (commonTypeSetoid a)
      (applyMorphism (applyMorphism (commonDependentPathLookup ctx paths a p) ps) (env, value))
      (applyMorphism (higherOrderTermSemantics w) env) ->
    DependentEndpointAtFace ctx p term ps env value

public export
dependentDeclaredLeftAtFace : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
  {0 decls : CommonDeclarations ctx paths} -> {p : LogicalVar paths a} -> {l, r : CommonTerm n} ->
  CommonDeclaredPath decls p l r -> (ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)) ->
  DependentPathAdmissible decls ps -> (env : carrier (commonEnvironmentSetoid ctx)) ->
  (valuation : Fin d -> DM) -> (face : ScopedFace d) -> (i : ScopedInterval d) ->
  boundedEndpointEntails face i False = True -> faceAtVal valuation face = True ->
  DependentEndpointAtFace ctx p l ps env (evalDMVal valuation i)
dependentDeclaredLeftAtFace declared ps admissible env valuation face i accepted holds =
  case dependentDeclaredLookup declared ps admissible of
    DependentEndpoints left right zero one =>
      DependentAtFace left (rewrite commonBoundedEndpointValSound valuation face i False accepted holds in zero env)

public export
dependentDeclaredRightAtFace : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
  {0 decls : CommonDeclarations ctx paths} -> {p : LogicalVar paths a} -> {l, r : CommonTerm n} ->
  CommonDeclaredPath decls p l r -> (ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)) ->
  DependentPathAdmissible decls ps -> (env : carrier (commonEnvironmentSetoid ctx)) ->
  (valuation : Fin d -> DM) -> (face : ScopedFace d) -> (i : ScopedInterval d) ->
  boundedEndpointEntails face i True = True -> faceAtVal valuation face = True ->
  DependentEndpointAtFace ctx p r ps env (evalDMVal valuation i)
dependentDeclaredRightAtFace declared ps admissible env valuation face i accepted holds =
  case dependentDeclaredLookup declared ps admissible of
    DependentEndpoints left right zero one =>
      DependentAtFace right (rewrite commonBoundedEndpointValSound valuation face i True accepted holds in one env)

||| A single witness is coherent with itself at related dependent environments.
public export
dependentPathSameWitness : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
  {a : LogicalType} -> {d : Nat} -> {0 t : CommonPathTerm n k d} ->
  {0 typing : CommonPathHasType ctx paths t a} -> (w : HigherOrderPathTerm ctx paths a d typing) ->
  (valuation : Fin d -> DM) -> morphismsRelated (dependentPathSemantics w valuation) (dependentPathSemantics w valuation)
dependentPathSameWitness w valuation x y xy = respectsRelation (dependentPathSemantics w valuation) xy

||| Alignment is indexed by the endpoint evidence actually extracted from admissibility.
public export
DependentEndpointAlignment : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} -> {a : LogicalType} ->
  {p : LogicalVar paths a} -> {term : CommonTerm n} ->
  {ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)} ->
  {env : carrier (commonEnvironmentSetoid ctx)} -> {value : DM} ->
  {0 ty : CommonHasType ctx term a} -> HigherOrderTerm ctx a ty ->
  DependentEndpointAtFace ctx p term ps env value -> Type
DependentEndpointAlignment selected (DependentAtFace actual _) = HigherOrderAlignment actual selected

||| Transport an extracted endpoint to a structurally aligned selected witness.
public export
dependentEndpointAligned : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} -> {a : LogicalType} ->
  {p : LogicalVar paths a} -> {term : CommonTerm n} ->
  {ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)} ->
  {env : carrier (commonEnvironmentSetoid ctx)} -> {value : DM} ->
  {0 ty : CommonHasType ctx term a} -> (selected : HigherOrderTerm ctx a ty) ->
  (endpoint : DependentEndpointAtFace ctx p term ps env value) ->
  DependentEndpointAlignment selected endpoint ->
  related (commonTypeSetoid a)
    (applyMorphism (applyMorphism (commonDependentPathLookup ctx paths a p) ps) (env, value))
    (applyMorphism (higherOrderTermSemantics selected) env)
dependentEndpointAligned {ctx} {a} {env} selected (DependentAtFace actual endpoint) alignment =
  relationTrans (commonTypeSetoid a) endpoint
    (higherOrderAlignedRelated alignment env env (relationRefl (commonEnvironmentSetoid ctx) env))

||| The alignment obligation refers to the endpoint chosen by this admissibility proof.
public export
dependentDeclaredLeftAlignedAtFace : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} -> {a : LogicalType} ->
  {0 decls : CommonDeclarations ctx paths} -> {p : LogicalVar paths a} -> {l, r : CommonTerm n} ->
  (declared : CommonDeclaredPath decls p l r) -> (ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)) ->
  (admissible : DependentPathAdmissible decls ps) -> (env : carrier (commonEnvironmentSetoid ctx)) ->
  (valuation : Fin d -> DM) -> (face : ScopedFace d) -> (i : ScopedInterval d) ->
  (accepted : boundedEndpointEntails face i False = True) -> (holds : faceAtVal valuation face = True) ->
  {0 ty : CommonHasType ctx l a} -> (selected : HigherOrderTerm ctx a ty) ->
  DependentEndpointAlignment selected (dependentDeclaredLeftAtFace declared ps admissible env valuation face i accepted holds) ->
  related (commonTypeSetoid a)
    (applyMorphism (applyMorphism (commonDependentPathLookup ctx paths a p) ps) (env, evalDMVal valuation i))
    (applyMorphism (higherOrderTermSemantics selected) env)
dependentDeclaredLeftAlignedAtFace declared ps admissible env valuation face i accepted holds selected alignment =
  dependentEndpointAligned selected (dependentDeclaredLeftAtFace declared ps admissible env valuation face i accepted holds) alignment

public export
dependentDeclaredRightAlignedAtFace : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} -> {a : LogicalType} ->
  {0 decls : CommonDeclarations ctx paths} -> {p : LogicalVar paths a} -> {l, r : CommonTerm n} ->
  (declared : CommonDeclaredPath decls p l r) -> (ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)) ->
  (admissible : DependentPathAdmissible decls ps) -> (env : carrier (commonEnvironmentSetoid ctx)) ->
  (valuation : Fin d -> DM) -> (face : ScopedFace d) -> (i : ScopedInterval d) ->
  (accepted : boundedEndpointEntails face i True = True) -> (holds : faceAtVal valuation face = True) ->
  {0 ty : CommonHasType ctx r a} -> (selected : HigherOrderTerm ctx a ty) ->
  DependentEndpointAlignment selected (dependentDeclaredRightAtFace declared ps admissible env valuation face i accepted holds) ->
  related (commonTypeSetoid a)
    (applyMorphism (applyMorphism (commonDependentPathLookup ctx paths a p) ps) (env, evalDMVal valuation i))
    (applyMorphism (higherOrderTermSemantics selected) env)
dependentDeclaredRightAlignedAtFace declared ps admissible env valuation face i accepted holds selected alignment =
  dependentEndpointAligned selected (dependentDeclaredRightAtFace declared ps admissible env valuation face i accepted holds) alignment

||| Structural evidence for the dependent higher-order fragment of a face derivation.
||| This fragment currently covers reflexivity, symmetry, transitivity and restriction.
public export
data DependentFaceEvidence : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
  {0 decls : CommonDeclarations ctx paths} -> {0 face : ScopedFace d} ->
  {0 x, y : CommonPathTerm n k d} -> {a : LogicalType} ->
  {0 lt : CommonPathHasType ctx paths x a} -> {0 rt : CommonPathHasType ctx paths y a} ->
  (0 eq : CommonFaceEqual decls face x y a) ->
  HigherOrderPathTerm ctx paths a d lt -> HigherOrderPathTerm ctx paths a d rt -> Type where
  DepFaceRefl : {0 lt, rt : CommonPathHasType ctx paths x a} ->
    {left : HigherOrderPathTerm ctx paths a d lt} -> {right : HigherOrderPathTerm ctx paths a d rt} ->
    HigherOrderPathAlignment left right -> DependentFaceEvidence (CommonRefl typed) left right
  DepFaceSym : DependentFaceEvidence eq l r -> DependentFaceEvidence (CommonSym eq) r l
  DepFaceTrans : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
    {0 x, y, z : CommonPathTerm n k d} -> {0 decls : CommonDeclarations ctx paths} ->
    {0 face : ScopedFace d} -> {a : LogicalType} ->
    {0 eq : CommonFaceEqual decls face x y a} -> {0 eq' : CommonFaceEqual decls face y z a} ->
    {0 lx : CommonPathHasType ctx paths x a} -> {0 rz : CommonPathHasType ctx paths z a} ->
    {l : HigherOrderPathTerm ctx paths a d lx} -> {r : HigherOrderPathTerm ctx paths a d rz} ->
    {0 mid, mid' : CommonPathHasType ctx paths y a} ->
    {m : HigherOrderPathTerm ctx paths a d mid} -> {m' : HigherOrderPathTerm ctx paths a d mid'} ->
    DependentFaceEvidence eq l m -> HigherOrderPathAlignment m m' -> DependentFaceEvidence eq' m' r ->
    DependentFaceEvidence (CommonTrans eq eq') l r
  DepFaceRestrict : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
    {0 x, y : CommonPathTerm n k d} -> {a : LogicalType} ->
    {0 lt : CommonPathHasType ctx paths x a} -> {0 rt : CommonPathHasType ctx paths y a} ->
    {l : HigherOrderPathTerm ctx paths a d lt} -> {r : HigherOrderPathTerm ctx paths a d rt} ->
    {0 decls : CommonDeclarations ctx paths} -> (face, source : ScopedFace d) ->
    {0 eq : CommonFaceEqual decls source x y a} -> (check : boundedFaceEntails face source = True) ->
    DependentFaceEvidence eq l r -> DependentFaceEvidence {face} (CommonRestrict eq check) l r

public export
dependentFaceEvidenceSound : {d : Nat} -> {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
  {0 decls : CommonDeclarations ctx paths} -> {face : ScopedFace d} ->
  {0 x, y : CommonPathTerm n k d} -> {a : LogicalType} ->
  {0 lt : CommonPathHasType ctx paths x a} -> {0 rt : CommonPathHasType ctx paths y a} ->
  {0 eq : CommonFaceEqual decls face x y a} ->
  {l : HigherOrderPathTerm ctx paths a d lt} -> {r : HigherOrderPathTerm ctx paths a d rt} ->
  DependentFaceEvidence eq l r -> (env : carrier (commonEnvironmentSetoid ctx)) ->
  (ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)) -> DependentPathAdmissible decls ps ->
  (valuation : Fin d -> DM) -> faceAtVal valuation face = True ->
  related (commonTypeSetoid a) (applyMorphism (dependentPathSemantics l valuation) (env, ps))
    (applyMorphism (dependentPathSemantics r valuation) (env, ps))
dependentFaceEvidenceSound {ctx} {paths} (DepFaceRefl alignment) env ps adm valuation holds =
  dependentPathAlignedRelated alignment valuation (env, ps) (env, ps)
    (relationRefl (commonProductSetoid (commonEnvironmentSetoid ctx) (commonDependentPathEnvironmentSetoid ctx paths)) (env, ps))
dependentFaceEvidenceSound {a} (DepFaceSym evidence) env ps adm valuation holds =
  relationSym (commonTypeSetoid a) (dependentFaceEvidenceSound evidence env ps adm valuation holds)
dependentFaceEvidenceSound {ctx} {paths} {a} (DepFaceTrans first alignment second) env ps adm valuation holds =
  relationTrans (commonTypeSetoid a) (dependentFaceEvidenceSound first env ps adm valuation holds)
    (relationTrans (commonTypeSetoid a)
      (dependentPathAlignedRelated alignment valuation (env, ps) (env, ps)
        (relationRefl (commonProductSetoid (commonEnvironmentSetoid ctx) (commonDependentPathEnvironmentSetoid ctx paths)) (env, ps)))
      (dependentFaceEvidenceSound second env ps adm valuation holds))
dependentFaceEvidenceSound (DepFaceRestrict face source check evidence) env ps adm valuation holds =
  dependentFaceEvidenceSound evidence env ps adm valuation (commonFaceValEntailsSound valuation face source check holds)

||| Endpoint evidence is indexed by the actual admissibility proof. The provider
||| aligns only syntax witnesses, uniformly over environments and face valuations.
public export
data DependentEndpointFaceEvidence : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
  {0 decls : CommonDeclarations ctx paths} -> {0 face : ScopedFace d} ->
  {0 x, y : CommonPathTerm n k d} -> {a : LogicalType} ->
  {0 lt : CommonPathHasType ctx paths x a} -> {0 rt : CommonPathHasType ctx paths y a} ->
  (0 eq : CommonFaceEqual decls face x y a) ->
  HigherOrderPathTerm ctx paths a d lt -> HigherOrderPathTerm ctx paths a d rt ->
  (ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)) -> DependentPathAdmissible decls ps -> Type where
  DepEndpointStructural : DependentFaceEvidence eq l r -> DependentEndpointFaceEvidence eq l r ps adm
  DepEndpointSym : DependentEndpointFaceEvidence eq l r ps adm ->
    DependentEndpointFaceEvidence (CommonSym eq) r l ps adm
  DepEndpointTrans : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
    {0 decls : CommonDeclarations ctx paths} -> {0 face : ScopedFace d} ->
    {0 x, y, z : CommonPathTerm n k d} -> {a : LogicalType} ->
    {0 eq : CommonFaceEqual decls face x y a} -> {0 eq' : CommonFaceEqual decls face y z a} ->
    {0 lx : CommonPathHasType ctx paths x a} -> {0 rz : CommonPathHasType ctx paths z a} ->
    {l : HigherOrderPathTerm ctx paths a d lx} -> {r : HigherOrderPathTerm ctx paths a d rz} ->
    {0 mid, mid' : CommonPathHasType ctx paths y a} ->
    {m : HigherOrderPathTerm ctx paths a d mid} -> {m' : HigherOrderPathTerm ctx paths a d mid'} ->
    {ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)} -> {adm : DependentPathAdmissible decls ps} ->
    DependentEndpointFaceEvidence eq l m ps adm -> HigherOrderPathAlignment m m' ->
    DependentEndpointFaceEvidence eq' m' r ps adm -> DependentEndpointFaceEvidence (CommonTrans eq eq') l r ps adm
  DepEndpointRestrict : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
    {0 x, y : CommonPathTerm n k d} -> {a : LogicalType} ->
    {0 lt : CommonPathHasType ctx paths x a} -> {0 rt : CommonPathHasType ctx paths y a} ->
    {l : HigherOrderPathTerm ctx paths a d lt} -> {r : HigherOrderPathTerm ctx paths a d rt} ->
    {0 decls : CommonDeclarations ctx paths} -> (face, source : ScopedFace d) ->
    {0 eq : CommonFaceEqual decls source x y a} -> (check : boundedFaceEntails face source = True) ->
    {ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)} -> {adm : DependentPathAdmissible decls ps} ->
    DependentEndpointFaceEvidence eq l r ps adm -> DependentEndpointFaceEvidence {face} (CommonRestrict eq check) l r ps adm
  DepEndpointLeft : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
    {0 decls : CommonDeclarations ctx paths} -> {face : ScopedFace d} -> {l, r : CommonTerm n} -> {0 typed : CommonHasType ctx l a} ->
    (p : LogicalVar paths a) -> (i : ScopedInterval d) -> (w : HigherOrderTerm ctx a typed) ->
    (declared : CommonDeclaredPath decls p l r) -> (check : boundedEndpointEntails face i False = True) ->
    (ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)) -> (adm : DependentPathAdmissible decls ps) ->
    ((env : carrier (commonEnvironmentSetoid ctx)) -> (valuation : Fin d -> DM) ->
      (holds : faceAtVal valuation face = True) ->
      DependentEndpointAlignment w (dependentDeclaredLeftAtFace declared ps adm env valuation face i check holds)) ->
    DependentEndpointFaceEvidence {face} (CommonLeft {i} declared check)
      (HOPAt ctx paths a d p i) (HOPOrdinary ctx paths a d w) ps adm
  DepEndpointRight : {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
    {0 decls : CommonDeclarations ctx paths} -> {face : ScopedFace d} -> {l, r : CommonTerm n} -> {0 typed : CommonHasType ctx r a} ->
    (p : LogicalVar paths a) -> (i : ScopedInterval d) -> (w : HigherOrderTerm ctx a typed) ->
    (declared : CommonDeclaredPath decls p l r) -> (check : boundedEndpointEntails face i True = True) ->
    (ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)) -> (adm : DependentPathAdmissible decls ps) ->
    ((env : carrier (commonEnvironmentSetoid ctx)) -> (valuation : Fin d -> DM) ->
      (holds : faceAtVal valuation face = True) ->
      DependentEndpointAlignment w (dependentDeclaredRightAtFace declared ps adm env valuation face i check holds)) ->
    DependentEndpointFaceEvidence {face} (CommonRight {i} declared check)
      (HOPAt ctx paths a d p i) (HOPOrdinary ctx paths a d w) ps adm

public export
dependentEndpointFaceEvidenceSound : {d : Nat} -> {ctx : Vect n LogicalType} -> {paths : Vect k LogicalType} ->
  {0 decls : CommonDeclarations ctx paths} -> {face : ScopedFace d} ->
  {0 x, y : CommonPathTerm n k d} -> {a : LogicalType} ->
  {0 lt : CommonPathHasType ctx paths x a} -> {0 rt : CommonPathHasType ctx paths y a} ->
  {0 eq : CommonFaceEqual decls face x y a} ->
  {l : HigherOrderPathTerm ctx paths a d lt} -> {r : HigherOrderPathTerm ctx paths a d rt} ->
  {ps : carrier (commonDependentPathEnvironmentSetoid ctx paths)} -> {adm : DependentPathAdmissible decls ps} ->
  DependentEndpointFaceEvidence eq l r ps adm -> (env : carrier (commonEnvironmentSetoid ctx)) ->
  (valuation : Fin d -> DM) -> faceAtVal valuation face = True ->
  related (commonTypeSetoid a) (applyMorphism (dependentPathSemantics l valuation) (env, ps))
    (applyMorphism (dependentPathSemantics r valuation) (env, ps))
dependentEndpointFaceEvidenceSound {ps} {adm} (DepEndpointStructural evidence) env valuation holds =
  dependentFaceEvidenceSound evidence env ps adm valuation holds
dependentEndpointFaceEvidenceSound {a} (DepEndpointSym evidence) env valuation holds =
  relationSym (commonTypeSetoid a) (dependentEndpointFaceEvidenceSound evidence env valuation holds)
dependentEndpointFaceEvidenceSound {ctx} {paths} {a} {ps} (DepEndpointTrans first alignment second) env valuation holds =
  relationTrans (commonTypeSetoid a) (dependentEndpointFaceEvidenceSound first env valuation holds)
    (relationTrans (commonTypeSetoid a)
      (dependentPathAlignedRelated alignment valuation (env, ps) (env, ps)
        (relationRefl (commonProductSetoid (commonEnvironmentSetoid ctx) (commonDependentPathEnvironmentSetoid ctx paths)) (env, ps)))
      (dependentEndpointFaceEvidenceSound second env valuation holds))
dependentEndpointFaceEvidenceSound (DepEndpointRestrict face source check evidence) env valuation holds =
  dependentEndpointFaceEvidenceSound evidence env valuation (commonFaceValEntailsSound valuation face source check holds)
dependentEndpointFaceEvidenceSound {face} (DepEndpointLeft p i w declared check ps adm alignment) env valuation holds =
  dependentDeclaredLeftAlignedAtFace declared ps adm env valuation face i check holds w (alignment env valuation holds)
dependentEndpointFaceEvidenceSound {face} (DepEndpointRight p i w declared check ps adm alignment) env valuation holds =
  dependentDeclaredRightAlignedAtFace declared ps adm env valuation face i check holds w (alignment env valuation holds)
