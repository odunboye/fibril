||| A type-preserving ordinary logical fragment. This is a declarative syntax,
||| not the runtime calculus or the abstract-base NeutralExpr checker.
module Fibril.Cubical.Logical.ShadowCommon

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Shadow
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
