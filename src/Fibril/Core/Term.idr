-- Scoped ordinary dependent-function, Unit, Boolean, and String syntax. This is not a type checker.
-- See docs/core-draft.md; cubical resource rules remain unresolved.
-- Theory: DEBRUIJN72 (nameless indices); ATKEY18 sec. 2 (QTT background, not implemented typing).
-- Bibliography and limitations: docs/references.md.
module Fibril.Core.Term

import Data.Fin
import Fibril.Core.Quantity

%default total

||| Terms in a context of n computational variables; 0 is newest.
||| Binder annotations are syntax, not evidence that usage has been checked.
public export
data Term : Nat -> Type where
  Variable : Fin n -> Term n
  Universe : Nat -> Term n
  ||| Primitive Unit : Type0; explicit case elimination, no eta rule (docs/unit.md).
  UnitType : Term n
  ||| Closed constructor () : Unit; zero runtime usage, not linear discard.
  UnitValue : Term n
  ||| Primitive Bool : Type0; distinct from cubical dimensions (docs/boolean.md).
  BoolType : Term n
  BoolTrue : Term n
  BoolFalse : Term n
  ||| Primitive String : Type0, literal data, and pure concatenation.
  StringType : Term n
  StringValue : String -> Term n
  StringAppend : Term n -> Term n -> Term n
  ||| Pure descriptions of effects; only the external runner performs writes.
  IOType : Term n -> Term n
  IOPure : Term n -> Term n
  IOBind : Term n -> Term n -> Term n -> Term n -> Term n
  WriteLine : Term n -> Term n
  ||| Nondependent branches; runtime checking joins their resource permissions.
  BoolCase : Term n -> Term n -> Term n -> Term n
  Pi : Quantity -> Term n -> Term (S n) -> Term n
  Lambda : Quantity -> Term n -> Term (S n) -> Term n
  Apply : Term n -> Term n -> Term n
  ||| Consume a Unit scrutinee, then return a body with no new pattern binders.
  UnitCase : Term n -> Term n -> Term n

||| Extend a renaming under one binder, preserving the newly bound variable.
public export
liftRenaming : (Fin n -> Fin m) -> Fin (S n) -> Fin (S m)
liftRenaming env FZ = FZ
liftRenaming env (FS i) = FS (env i)

||| Rename free variables; domain annotations remain outside the binder scope.
public export
rename : (Fin n -> Fin m) -> Term n -> Term m
rename env (Variable i) = Variable (env i)
rename env (Universe l) = Universe l
rename env UnitType = UnitType
rename env UnitValue = UnitValue
rename env BoolType = BoolType
rename env BoolTrue = BoolTrue
rename env BoolFalse = BoolFalse
rename env StringType = StringType
rename env (StringValue value) = StringValue value
rename env (StringAppend left right) = StringAppend (rename env left) (rename env right)
rename env (IOType ty) = IOType (rename env ty)
rename env (IOPure value) = IOPure (rename env value)
rename env (WriteLine text) = WriteLine (rename env text)
rename env (IOBind a b action next) =
  IOBind (rename env a) (rename env b) (rename env action) (rename env next)
rename env (BoolCase condition yes no) =
  BoolCase (rename env condition) (rename env yes) (rename env no)
rename env (Pi q domain body) =
  Pi q (rename env domain) (rename (liftRenaming env) body)
rename env (Lambda q domain body) =
  Lambda q (rename env domain) (rename (liftRenaming env) body)
rename env (Apply f x) = Apply (rename env f) (rename env x)
rename env (UnitCase scrutinee body) = UnitCase (rename env scrutinee) (rename env body)

||| Insert a newest variable, shifting all existing free references.
public export
weaken : Term n -> Term (S n)
weaken = rename FS

||| Extend substitution under a binder, weakening replacements to avoid capture.
public export
liftSubstitution : (Fin n -> Term m) -> Fin (S n) -> Term (S m)
liftSubstitution env FZ = Variable FZ
liftSubstitution env (FS i) = weaken (env i)

||| Simultaneous capture-avoiding substitution; performs no reduction.
public export
substituteTerm : (Fin n -> Term m) -> Term n -> Term m
substituteTerm env (Variable i) = env i
substituteTerm env (Universe l) = Universe l
substituteTerm env UnitType = UnitType
substituteTerm env UnitValue = UnitValue
substituteTerm env BoolType = BoolType
substituteTerm env BoolTrue = BoolTrue
substituteTerm env BoolFalse = BoolFalse
substituteTerm env StringType = StringType
substituteTerm env (StringValue value) = StringValue value
substituteTerm env (StringAppend left right) =
  StringAppend (substituteTerm env left) (substituteTerm env right)
substituteTerm env (IOType ty) = IOType (substituteTerm env ty)
substituteTerm env (IOPure value) = IOPure (substituteTerm env value)
substituteTerm env (WriteLine text) = WriteLine (substituteTerm env text)
substituteTerm env (IOBind a b action next) =
  IOBind (substituteTerm env a) (substituteTerm env b)
         (substituteTerm env action) (substituteTerm env next)
substituteTerm env (BoolCase condition yes no) =
  BoolCase (substituteTerm env condition) (substituteTerm env yes) (substituteTerm env no)
substituteTerm env (Pi q domain body) =
  Pi q (substituteTerm env domain) (substituteTerm (liftSubstitution env) body)
substituteTerm env (Lambda q domain body) =
  Lambda q (substituteTerm env domain) (substituteTerm (liftSubstitution env) body)
substituteTerm env (Apply f x) = Apply (substituteTerm env f) (substituteTerm env x)
substituteTerm env (UnitCase scrutinee body) =
  UnitCase (substituteTerm env scrutinee) (substituteTerm env body)

||| Replacement map for removing the newest variable from a scope.
||| Factored out so structural proofs use the exact same map as instantiation.
public export
replaceNewest : Term n -> Fin (S n) -> Term n
replaceNewest value FZ = value
replaceNewest value (FS i) = Variable i

||| Replace the newest free variable; older indices shift down.
||| This is a syntactic operation, not a checked beta-reduction rule.
public export
instantiateTerm : Term n -> Term (S n) -> Term n
instantiateTerm value = substituteTerm (replaceNewest value)

||| Structural syntax equality only, not definitional equality or path equality.
public export
sameSyntax : Term n -> Term n -> Bool
sameSyntax (Variable i) (Variable j) = i == j
sameSyntax (Universe l) (Universe k) = l == k
sameSyntax UnitType UnitType = True
sameSyntax UnitValue UnitValue = True
sameSyntax BoolType BoolType = True
sameSyntax BoolTrue BoolTrue = True
sameSyntax BoolFalse BoolFalse = True
sameSyntax StringType StringType = True
sameSyntax (StringValue left) (StringValue right) = left == right
sameSyntax (StringAppend a b) (StringAppend c d) = sameSyntax a c && sameSyntax b d
sameSyntax (IOType a) (IOType b) = sameSyntax a b
sameSyntax (IOPure a) (IOPure b) = sameSyntax a b
sameSyntax (WriteLine a) (WriteLine b) = sameSyntax a b
sameSyntax (IOBind a b c d) (IOBind e f g h) =
  sameSyntax a e && sameSyntax b f && sameSyntax c g && sameSyntax d h
sameSyntax (BoolCase c t e) (BoolCase d u f) =
  sameSyntax c d && sameSyntax t u && sameSyntax e f
sameSyntax (Pi q a b) (Pi r c d) = q == r && sameSyntax a c && sameSyntax b d
sameSyntax (Lambda q a b) (Lambda r c d) = q == r && sameSyntax a c && sameSyntax b d
sameSyntax (Apply f x) (Apply g y) = sameSyntax f g && sameSyntax x y
sameSyntax (UnitCase u b) (UnitCase v c) = sameSyntax u v && sameSyntax b c
sameSyntax _ _ = False
