module Fibril.Core.Quantitative.CoreTranslation

import Data.Fin
import Data.Vect
import Fibril.Core.Quantity
import Fibril.Core.Context
import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Term

%default total

||| Recover the otherwise erased application domain indices needed for Core
||| lambda annotations. This is structural evidence, not a typing check.
public export
data Annotations : {0 n : Nat} -> {0 context : Vect n Ty} ->
                   {0 ty : Ty} -> Quantitative.Syntax.Term context ty -> Type where
  ARef : Annotations (Ref v)
  AUnit : Annotations Unit
  ABoolean : Annotations (Boolean b)
  ALam : {0 context : Vect n Ty} -> {0 a, b : Ty} ->
         {0 body : Quantitative.Syntax.Term (a :: context) b} ->
         Annotations body -> Annotations (Lam q body)
  AApp : {0 context : Vect n Ty} -> {0 b : Ty} -> {q : Quantity} ->
         (domain : Ty) -> {0 fun : Quantitative.Syntax.Term context (Arrow q domain b)} ->
         {0 arg : Quantitative.Syntax.Term context domain} ->
         Annotations fun -> Annotations arg -> Annotations (App fun arg)
  AUnitElim : {0 context : Vect n Ty} -> {0 ty : Ty} ->
              {0 scrutinee : Quantitative.Syntax.Term context UnitTy} ->
              {0 body : Quantitative.Syntax.Term context ty} ->
              Annotations scrutinee -> Annotations body -> Annotations (UnitElim scrutinee body)
  AIf : {0 context : Vect n Ty} -> {0 ty : Ty} ->
        {0 cond : Quantitative.Syntax.Term context BoolTy} ->
        {0 yes, no : Quantitative.Syntax.Term context ty} ->
        Annotations cond -> Annotations yes -> Annotations no -> Annotations (If cond yes no)

public export
coreType : Ty -> Core.Term.Term n
coreType UnitTy = UnitType
coreType BoolTy = BoolType
coreType (Arrow q a b) = Pi q (coreType a) (coreType b)

public export
coreVar : {0 context : Vect n Ty} -> Var context ty -> Fin n
coreVar Here = FZ
coreVar (There v) = FS (coreVar v)

||| The context and permissions have identical newest-first indexing.
public export
coreContext : Vect n Ty -> Vect n Quantity -> Context n
coreContext [] [] = Empty
coreContext (ty :: rest) (q :: qs) = Extend (coreContext rest qs) q (coreType ty)

public export
coreTerm : {0 context : Vect n Ty} -> (ty : Ty) -> (term : Quantitative.Syntax.Term context ty) ->
           Annotations term -> Core.Term.Term n
coreTerm ty (Ref v) ARef = Variable (coreVar v)
coreTerm UnitTy Unit AUnit = UnitValue
coreTerm BoolTy (Boolean True) ABoolean = BoolTrue
coreTerm BoolTy (Boolean False) ABoolean = BoolFalse
coreTerm (Arrow q a b) (Lam q body) (ALam ann) = Lambda q (coreType a) (coreTerm b body ann)
coreTerm ty (App {q} fun arg) (AApp domain f x) =
  Apply (coreTerm (Arrow q domain ty) fun f) (coreTerm domain arg x)
coreTerm ty (UnitElim scrutinee body) (AUnitElim s b) = UnitCase (coreTerm UnitTy scrutinee s) (coreTerm ty body b)
coreTerm ty (If cond yes no) (AIf c y n) = BoolCase (coreTerm BoolTy cond c) (coreTerm ty yes y) (coreTerm ty no n)

||| Context translation preserves the declared permission at every scoped variable.
public export
coreContextQuantity : (types : Vect n Ty) -> (permissions : Vect n Quantity) ->
  (variable : Var types ty) ->
  lookupQuantity (coreVar variable) (coreContext types permissions) =
    index (coreVar variable) permissions
coreContextQuantity (ty :: rest) (q :: qs) Here = Refl
coreContextQuantity (ty :: rest) (q :: qs) (There variable) =
  coreContextQuantity rest qs variable
