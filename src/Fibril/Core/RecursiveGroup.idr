-- Raw scoped recursive-group syntax. No typing, termination, or execution.
module Fibril.Core.RecursiveGroup

import Data.Fin
import Data.Vect
import Fibril.Core.Term

%default total

||| First-order recursive bodies over a fixed group. `arities` is in member
||| order. Locals are scoped separately from group members; member calls cannot
||| be represented by a local variable. A call has exactly the target arity.
|||
||| Embedded ordinary terms have no recursive-group constructor in the current
||| core. They are still untrusted: they may be ill typed, effectful, or contain
||| unsupported higher-order operations. This syntax grants no admission.
public export
data Body : {members : Nat} -> Vect members Nat -> Nat -> Type where
  Return : Term locals -> Body arities locals
  Call : (target : Fin members) -> Vect (index target arities) (Term locals) -> Body arities locals
  ||| Successor introduces its predecessor as local 0.
  CaseNat : Term locals -> Body arities locals -> Body arities (S locals) -> Body arities locals
  ||| The cons branch has tail at local 0, head at local 1.
  CaseList : Term locals -> Body arities locals -> Body arities (S (S locals)) -> Body arities locals
  CaseBool : Term locals -> Body arities locals -> Body arities locals -> Body arities locals

||| A member stores a closed signature and a body scoped over exactly its
||| declared number of parameters. No claim is made that the signature is a
||| well-formed Pi telescope with that arity, or that the body has its type.
public export
record Member {members : Nat} (arities : Vect members Nat) (arity : Nat) where
  constructor MkMember
  signature : Term 0
  body : Body arities arity

||| An ordered heterogeneous member collection. Its arity vector must agree
||| with the group's arity vector, but individual entries are otherwise raw.
public export
data Members : {count, remaining : Nat} -> Vect count Nat -> Vect remaining Nat -> Type where
  NoMembers : Members arities []
  MoreMembers : Member arities arity -> Members arities rest -> Members arities (arity :: rest)

||| Group positions are stable only within this exact value. No hashes, names,
||| certificates, or checked flags are authority. Empty raw groups are allowed;
||| any eventual admission policy must decide whether they are useful.
public export
record Group (count : Nat) where
  constructor MkGroup
  arities : Vect count Nat
  definitions : Members arities arities

lookupWithin : (remaining : Vect n Nat) -> Members shape remaining ->
               (position : Fin n) -> Member shape (index position remaining)
lookupWithin (_ :: _) (MoreMembers member _) FZ = member
lookupWithin (_ :: rest) (MoreMembers _ following) (FS position) = lookupWithin rest following position

||| Look up the exact member selected by a group position. The result's body
||| scope is indexed by that same position's declared arity.
public export
memberAt : (group : Group size) -> (position : Fin size) -> Member group.arities (index position group.arities)
memberAt group position = lookupWithin group.arities group.definitions position

||| Rename ordinary locals only; member indices and saturation do not change.
||| Pattern binders are preserved by lifting the renaming under each binder.
public export
renameBody : (Fin n -> Fin m) -> Body shape n -> Body shape m
renameBody env (Return value) = Return (rename env value)
renameBody env (Call target args) = Call target (map (rename env) args)
renameBody env (CaseNat value zero successor) =
  CaseNat (rename env value) (renameBody env zero) (renameBody (liftRenaming env) successor)
renameBody env (CaseList value nil cons) =
  CaseList (rename env value) (renameBody env nil) (renameBody (liftRenaming (liftRenaming env)) cons)
renameBody env (CaseBool condition yes no) =
  CaseBool (rename env condition) (renameBody env yes) (renameBody env no)

||| Capture-avoiding simultaneous substitution of ordinary locals. Calls stay
||| calls; this does not unfold a member or reduce any embedded term.
public export
substituteBody : (Fin n -> Term m) -> Body shape n -> Body shape m
substituteBody env (Return value) = Return (substituteTerm env value)
substituteBody env (Call target args) = Call target (map (substituteTerm env) args)
substituteBody env (CaseNat value zero successor) =
  CaseNat (substituteTerm env value) (substituteBody env zero) (substituteBody (liftSubstitution env) successor)
substituteBody env (CaseList value nil cons) =
  CaseList (substituteTerm env value) (substituteBody env nil) (substituteBody (liftSubstitution (liftSubstitution env)) cons)
substituteBody env (CaseBool condition yes no) =
  CaseBool (substituteTerm env condition) (substituteBody env yes) (substituteBody env no)
