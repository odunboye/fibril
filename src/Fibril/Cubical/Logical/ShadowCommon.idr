||| A type-preserving ordinary logical fragment. This is a declarative syntax,
||| not the runtime calculus or the abstract-base NeutralExpr checker.
module Fibril.Cubical.Logical.ShadowCommon

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
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
