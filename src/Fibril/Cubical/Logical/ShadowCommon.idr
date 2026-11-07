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

public export
data CommonHasType : Vect n LogicalType -> CommonTerm n -> LogicalType -> Type where
  CVariable : (v : LogicalVar ctx a) -> CommonHasType ctx (CVar (variableIndex v)) a
  CUnitType : CommonHasType ctx CUnit LUnit
  CBoolType : CommonHasType ctx (CBool b) LBool
  CLambdaType : CommonHasType (a :: ctx) body b -> CommonHasType ctx (CLam body) (LArrow a b)
  CApplicationType : CommonHasType ctx f (LArrow a b) -> CommonHasType ctx x a -> CommonHasType ctx (CApp f x) b
  CUnitEliminationType : CommonHasType ctx x LUnit -> CommonHasType ctx body a -> CommonHasType ctx (CUnitElim x body) a
  CConditionalType : CommonHasType ctx c LBool -> CommonHasType ctx t a -> CommonHasType ctx f a -> CommonHasType ctx (CIf c t f) a

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

public export
data CommonPathHasType : Vect n LogicalType -> Vect k LogicalType -> CommonPathTerm n k d -> LogicalType -> Type where
  CPOrdinaryType : CommonHasType ctx t a -> CommonPathHasType ctx paths (CPOrdinary t) a
  CPAtType : (p : LogicalVar paths a) -> CommonPathHasType ctx paths (CPAt (variableIndex p) i) a
  CPLamType : CommonPathHasType (a :: ctx) paths b c -> CommonPathHasType ctx paths (CPLam b) (LArrow a c)
  CPAppType : CommonPathHasType ctx paths f (LArrow a b) -> CommonPathHasType ctx paths x a -> CommonPathHasType ctx paths (CPApp f x) b
  CPUnitElimType : CommonPathHasType ctx paths x LUnit -> CommonPathHasType ctx paths b a -> CommonPathHasType ctx paths (CPUnitElim x b) a
  CPIfType : CommonPathHasType ctx paths c LBool -> CommonPathHasType ctx paths t a -> CommonPathHasType ctx paths f a -> CommonPathHasType ctx paths (CPIf c t f) a

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
  CommonPathTerm n k d -> CommonPathTerm n k d -> LogicalType -> Type where
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
