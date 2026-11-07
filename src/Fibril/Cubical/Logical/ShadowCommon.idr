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
firstOrderFaceEqualSound (FOFaceRestrict face source check eq) env ps adm valuation holds =
  firstOrderFaceEqualSound eq env ps adm valuation (commonFaceValEntailsSound valuation face source check holds)
firstOrderFaceEqualSound (FOFaceLeft p i w declared check) env ps adm valuation holds =
  case firstOrderDeclaredLeftAtFace declared ps adm env valuation _ i check holds of
    FOLeftAtFace left prf => trans prf (firstOrderTermCoherent left w env)
firstOrderFaceEqualSound (FOFaceRight p i w declared check) env ps adm valuation holds =
  case firstOrderDeclaredRightAtFace declared ps adm env valuation _ i check holds of
    FORightAtFace right prf => trans prf (firstOrderTermCoherent right w env)
