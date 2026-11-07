-- Untrusted size-change extraction from restricted checked recursive groups.
module Fibril.Termination.GroupCalls

import Data.Fin
import Data.List
import Data.Vect
import Fibril.Core.RecursiveGroup
import Fibril.Core.RecursiveGroupCheck
import Fibril.Core.Term
import Fibril.Termination.SizeChange

%default total

||| A group must first pass the restricted ordinary type and usage checker.
||| Extraction is still untrusted and does not authorize recursive execution.
public export
data ExtractionProblem = GroupProblem Problem | UnsupportedBody String

indices : Nat -> List Nat
indices count = map finToNat (toList (Data.Vect.allFins count))

initialRows : (width : Nat) -> Vect width (List Relation)
initialRows width = reverse (map (\i => map (\j => if finToNat i == j then NonIncreasing else Unknown) (indices width)) (Data.Vect.allFins width))

-- Only an unchanged local has a known relation. Constructed values are
-- conservatively unknown, including NatZero and NatSucc.
row : Nat -> Vect n (List Relation) -> Term n -> List Relation
row width env (Variable position) = Data.Vect.index position env
row width env _ = replicate width Unknown

smaller : Relation -> Relation
smaller Unknown = Unknown
smaller NonIncreasing = Decreases
smaller Decreases = Decreases

walk : Nat -> Nat -> Vect n (List Relation) -> Body groupShape n -> List Call -> Either ExtractionProblem (List Call)
walk caller width env (Return _) calls = Right calls
walk caller width env (Call target args) calls =
  Right (Edge caller (finToNat target) (map (row width env) (toList args)) :: calls)
walk caller width env (CaseNat value zero successor) calls = do
  calls <- walk caller width env zero calls
  walk caller width (map smaller (row width env value) :: env) successor calls
walk caller width env (CaseBool value yes no) calls = do
  calls <- walk caller width env yes calls
  walk caller width env no calls
walk _ _ _ (CaseList _ _ _) _ = Left (UnsupportedBody "list cases are not supported by group typing")

walkMembers : Nat -> (remaining : Vect n Nat) -> Members groupShape remaining -> List Call -> Either ExtractionProblem (List Call)
walkMembers caller [] NoMembers calls = Right (reverse calls)
walkMembers caller (arity :: rest) (MoreMembers member following) calls = do
  calls <- walk caller arity (initialRows arity) member.body calls
  walkMembers (S caller) rest following calls

||| Extract one matrix per actual call site, in member and branch order.
||| The group checker bounds the walk, but this producer remains untrusted.
public export
extract : (group : Group size) -> Either ExtractionProblem (List Call)
extract group = do
  case Fibril.Core.RecursiveGroupCheck.check group of
    Left problem => Left (GroupProblem problem)
    Right () => Right ()
  walkMembers 0 group.arities group.definitions []
