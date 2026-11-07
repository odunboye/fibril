module Fibril.Cubical.Logical.Shadow

import Data.Vect
import Fibril.Core.Quantitative.Syntax

%default total

||| Pure logical types; no quantitative annotation survives here.
public export
data LogicalType = LUnit | LBool | LArrow LogicalType LogicalType

public export
shadowType : Ty -> LogicalType
shadowType UnitTy = LUnit
shadowType BoolTy = LBool
shadowType (Arrow q a b) = LArrow (shadowType a) (shadowType b)

public export
shadowContext : Vect n Ty -> Vect n LogicalType
shadowContext = map shadowType

public export
data LogicalVar : (0 context : Vect n LogicalType) -> (0 ty : LogicalType) -> Type where
  LHere : LogicalVar (a :: context) a
  LThere : LogicalVar context a -> LogicalVar (b :: context) a

public export
data LogicalTerm : (0 context : Vect n LogicalType) -> (0 ty : LogicalType) -> Type where
  LRef : LogicalVar context a -> LogicalTerm context a
  LUnitValue : LogicalTerm context LUnit
  LBoolean : Bool -> LogicalTerm context LBool
  LLam : LogicalTerm (a :: context) b -> LogicalTerm context (LArrow a b)
  LApp : LogicalTerm context (LArrow a b) -> LogicalTerm context a -> LogicalTerm context b
  LUnitElim : LogicalTerm context LUnit -> LogicalTerm context a -> LogicalTerm context a
  LIf : LogicalTerm context LBool -> LogicalTerm context a -> LogicalTerm context a -> LogicalTerm context a

public export
shadowVar : {0 context : Vect n Ty} -> Var context a -> LogicalVar (shadowContext context) (shadowType a)
shadowVar Here = LHere
shadowVar (There v) = LThere (shadowVar v)

||| Total intrinsic typing of the pure source shadow, independent of Uses.
public export
shadowTerm : {0 context : Vect n Ty} -> Term context a -> LogicalTerm (shadowContext context) (shadowType a)
shadowTerm (Ref v) = LRef (shadowVar v)
shadowTerm Unit = LUnitValue
shadowTerm (Boolean b) = LBoolean b
shadowTerm (Lam q body) = LLam (shadowTerm body)
shadowTerm (App f x) = LApp (shadowTerm f) (shadowTerm x)
shadowTerm (UnitElim x body) = LUnitElim (shadowTerm x) (shadowTerm body)
shadowTerm (If c t f) = LIf (shadowTerm c) (shadowTerm t) (shadowTerm f)

public export
LogicalRenaming : Vect n LogicalType -> Vect m LogicalType -> Type
LogicalRenaming source target = {0 ty : LogicalType} -> LogicalVar source ty -> LogicalVar target ty

public export
liftLogicalRenaming : LogicalRenaming source target -> LogicalRenaming (a :: source) (a :: target)
liftLogicalRenaming rho LHere = LHere
liftLogicalRenaming rho (LThere v) = LThere (rho v)

public export
renameLogical : LogicalRenaming source target -> LogicalTerm source a -> LogicalTerm target a
renameLogical rho (LRef v) = LRef (rho v)
renameLogical rho LUnitValue = LUnitValue
renameLogical rho (LBoolean b) = LBoolean b
renameLogical rho (LLam body) = LLam (renameLogical (liftLogicalRenaming rho) body)
renameLogical rho (LApp f x) = LApp (renameLogical rho f) (renameLogical rho x)
renameLogical rho (LUnitElim x body) = LUnitElim (renameLogical rho x) (renameLogical rho body)
renameLogical rho (LIf c t f) = LIf (renameLogical rho c) (renameLogical rho t) (renameLogical rho f)

public export
LogicalSubstitution : Vect n LogicalType -> Vect m LogicalType -> Type
LogicalSubstitution source target = {0 ty : LogicalType} -> LogicalVar source ty -> LogicalTerm target ty

public export
liftLogicalSubstitution : LogicalSubstitution source target -> LogicalSubstitution (a :: source) (a :: target)
liftLogicalSubstitution sigma LHere = LRef LHere
liftLogicalSubstitution sigma (LThere v) = renameLogical LThere (sigma v)

||| Simultaneous substitution preserves logical typing by construction.
public export
substituteLogical : LogicalSubstitution source target -> LogicalTerm source a -> LogicalTerm target a
substituteLogical sigma (LRef v) = sigma v
substituteLogical sigma LUnitValue = LUnitValue
substituteLogical sigma (LBoolean b) = LBoolean b
substituteLogical sigma (LLam body) = LLam (substituteLogical (liftLogicalSubstitution sigma) body)
substituteLogical sigma (LApp f x) = LApp (substituteLogical sigma f) (substituteLogical sigma x)
substituteLogical sigma (LUnitElim x body) = LUnitElim (substituteLogical sigma x) (substituteLogical sigma body)
substituteLogical sigma (LIf c t f) = LIf (substituteLogical sigma c) (substituteLogical sigma t) (substituteLogical sigma f)
