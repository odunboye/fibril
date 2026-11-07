module Fibril.Core.Quantitative.Syntax

import Data.Vect
import Fibril.Core.Quantity

%default total

||| Isolated pure, nondependent types. Quantities remain part of function types.
public export
data Ty = UnitTy | BoolTy | Arrow Quantity Ty Ty

||| Contexts are newest first. Here denotes the most recently bound variable.
public export
data Var : (0 context : Vect n Ty) -> (0 ty : Ty) -> Type where
  Here : Var (a :: context) a
  There : Var context a -> Var (b :: context) a

||| Intrinsic simple typing only: this syntax does NOT enforce resource usage.
||| There are no effects, globals, dependencies, paths, or unchecked annotations.
public export
data Term : (0 context : Vect n Ty) -> (0 ty : Ty) -> Type where
  Ref : Var context a -> Term context a
  Unit : Term context UnitTy
  Boolean : Bool -> Term context BoolTy
  Lam : (q : Quantity) -> Term (a :: context) b -> Term context (Arrow q a b)
  App : {q : Quantity} -> Term context (Arrow q a b) -> Term context a -> Term context b
  UnitElim : Term context UnitTy -> Term context a -> Term context a
  If : Term context BoolTy -> Term context a -> Term context a -> Term context a
