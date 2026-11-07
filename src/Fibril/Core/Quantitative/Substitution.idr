module Fibril.Core.Quantitative.Substitution

import Data.Vect
import Fibril.Core.Quantitative.Syntax

%default total

||| Every source variable maps to a destination variable of the SAME type.
||| This permits contraction and weakening, not just resource-safe renaming.
public export
Renaming : Vect n Ty -> Vect m Ty -> Type
Renaming source target = {0 ty : Ty} -> Var source ty -> Var target ty

public export
liftRenaming : Renaming source target -> Renaming (a :: source) (a :: target)
liftRenaming rho Here = Here
liftRenaming rho (There variable) = There (rho variable)

||| A total typed renaming theorem by construction, not a quantitative theorem.
public export
rename : Renaming source target -> Term source a -> Term target a
rename rho (Ref variable) = Ref (rho variable)
rename rho Unit = Unit
rename rho (Boolean value) = Boolean value
rename rho (Lam q body) = Lam q (rename (liftRenaming rho) body)
rename rho (App {q} function argument) = App {q} (rename rho function) (rename rho argument)
rename rho (UnitElim value body) = UnitElim (rename rho value) (rename rho body)
rename rho (If condition yes no) = If (rename rho condition) (rename rho yes) (rename rho no)

public export
weaken : Term context a -> Term (b :: context) a
weaken = rename There

||| Typed simultaneous replacements; no usage-row premise is imposed here.
public export
Substitution : Vect n Ty -> Vect m Ty -> Type
Substitution source target = {0 ty : Ty} -> Var source ty -> Term target ty

||| Preserve the new binder and weaken ALL outer replacements under it.
public export
liftSubstitution : Substitution source target -> Substitution (a :: source) (a :: target)
liftSubstitution sigma Here = Ref Here
liftSubstitution sigma (There variable) = weaken (sigma variable)

||| If sigma maps G variables to same-typed terms in D, t : A in G
||| yields substitute sigma t : A in D. No quantitative preservation is claimed.
public export
substitute : Substitution source target -> Term source a -> Term target a
substitute sigma (Ref variable) = sigma variable
substitute sigma Unit = Unit
substitute sigma (Boolean value) = Boolean value
substitute sigma (Lam q body) = Lam q (substitute (liftSubstitution sigma) body)
substitute sigma (App {q} function argument) = App {q} (substitute sigma function) (substitute sigma argument)
substitute sigma (UnitElim value body) = UnitElim (substitute sigma value) (substitute sigma body)
substitute sigma (If condition yes no) = If (substitute sigma condition) (substitute sigma yes) (substitute sigma no)

public export
headSubstitution : Term context a -> Substitution (a :: context) context
headSubstitution value Here = value
headSubstitution value (There variable) = Ref variable

||| Head substitution discharges the NEWEST variable. Both input and output
||| are intrinsically simply typed; usage and internal binder checks are separate.
public export
instantiate : Term context a -> Term (a :: context) b -> Term context b
instantiate value body = substitute (headSubstitution value) body
