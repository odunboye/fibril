-- Independent provenance rewalk for restricted actual recursive groups.
-- This checks graph/body correspondence, not recursive core execution.
module Fibril.Termination.GroupCheck

import Data.Fin
import Data.List
import Data.Vect
import Fibril.Core.RecursiveGroup
import Fibril.Core.RecursiveGroupCheck
import Fibril.Core.Term
import Fibril.Termination.SizeChange

%default total

public export
data GraphProblem = GroupProblem Problem | GraphMismatch String | GraphAdmission String

-- The checker tracks origin identities, not the producer's relation rows.
private
data Origin = Root Nat | Descendant Nat | NoOrigin

origin : Vect n Origin -> Term n -> Origin
origin env (Variable position) = Data.Vect.index position env
origin _ _ = NoOrigin

descendant : Origin -> Origin
descendant (Root index) = Descendant index
descendant (Descendant index) = Descendant index
descendant NoOrigin = NoOrigin

relation : Origin -> Nat -> Relation
relation (Root index) column = if index == column then NonIncreasing else Unknown
relation (Descendant index) column = if index == column then Decreases else Unknown
relation NoOrigin _ = Unknown

indices : Nat -> List Nat
indices width = map finToNat (toList (Data.Vect.allFins width))

initialOrigins : (width : Nat) -> Vect width Origin
initialOrigins width = reverse (map (Root . finToNat) (Data.Vect.allFins width))

matches : Nat -> Vect n Origin -> Term n -> List Relation -> Bool
matches width env argument row = row == map (relation (origin env argument)) (indices width)

matchesArgs : Nat -> Vect n Origin -> Vect arity (Term n) -> List (List Relation) -> Bool
matchesArgs width env [] [] = True
matchesArgs width env (arg :: args) (row :: rows) =
  matches width env arg row && matchesArgs width env args rows
matchesArgs _ _ _ _ = False

walk : Nat -> Nat -> Vect n Origin -> Body groupShape n -> List Call -> Either GraphProblem (List Call)
walk caller width env (Return _) calls = Right calls
walk caller width env (Call target args) [] = Left (GraphMismatch "proposed graph omits a call site")
walk caller width env (Call target args) (edge :: rest) =
  if edge.caller == caller && edge.callee == finToNat target && matchesArgs width env args edge.matrix
    then Right rest else Left (GraphMismatch "proposed call site does not match the group")
walk caller width env (CaseNat value zero successor) calls = do
  calls <- walk caller width env zero calls
  walk caller width (descendant (origin env value) :: env) successor calls
walk caller width env (CaseBool value yes no) calls = do
  calls <- walk caller width env yes calls
  walk caller width env no calls
walk _ _ _ (CaseList _ _ _) _ = Left (GraphMismatch "list cases are not supported by group typing")

walkMembers : Nat -> (remaining : Vect n Nat) -> Members groupShape remaining -> List Call -> Either GraphProblem (List Call)
walkMembers caller [] NoMembers calls = Right calls
walkMembers caller (arity :: rest) (MoreMembers member following) calls = do
  calls <- walk caller arity (initialOrigins arity) member.body calls
  walkMembers (S caller) rest following calls

within : Nat -> List a -> Bool
within Z [] = True
within Z (_ :: _) = False
within (S _) [] = True
within (S fuel) (_ :: rest) = within fuel rest

||| Recheck the exact group and every proposed call site in syntax order.
||| This is not an authorization to execute or admit a recursive definition.
public export
check : (group : Group size) -> List Call -> Either GraphProblem ()
check group proposed = do
  case Fibril.Core.RecursiveGroupCheck.check group of
    Left problem => Left (GroupProblem problem)
    Right () => Right ()
  if within 128 proposed then Right () else Left (GraphAdmission "proposed call admission exhausted (128)")
  if all (\edge => within 8 edge.matrix && all (within 8) edge.matrix) proposed
    then Right () else Left (GraphMismatch "proposed matrix exceeds shape admission")
  remaining <- walkMembers 0 group.arities group.definitions proposed
  if null remaining then Right () else Left (GraphMismatch "proposed graph contains extra call sites")

||| Verify a closure only after independently rechecking all calls against the
||| same group. GraphAccepted is still not recursive evaluation or admission.
public export
verifyGroup : (group : Group size) -> List Call -> List Call -> Either GraphProblem Verdict
verifyGroup group proposed certificate = do
  check group proposed
  Right (verify (toList group.arities) proposed certificate)
