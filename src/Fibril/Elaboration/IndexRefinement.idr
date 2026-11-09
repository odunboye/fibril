-- Untrusted index-directed motive inference. Every synthesized case still has
-- all constructor arms and is independently checked by Core.Erased/Runtime.
module Fibril.Elaboration.IndexRefinement

import Data.Fin
import Data.List
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.DataDecl
import Fibril.Core.Erased
import Fibril.Core.Reduction
import Fibril.Elaboration.Expression.Abstract

%default total

natPattern : Nat -> Term n -> Bool
natPattern Z _ = False
natPattern (S fuel) (Variable _) = True
natPattern (S fuel) NatZero = True
natPattern (S fuel) (NatSucc rest) = True
natPattern _ _ = False

-- At nonmatching indices, return the original family. Reconstructing an
-- unreachable constructor then remains a well-typed, ownership-preserving arm.
refineType : Nat -> Term n -> Term n -> Term n -> Term n -> Maybe (Term n)
refineType Z pattern value result fallback = Nothing
refineType (S fuel) pattern@(Variable _) value result fallback =
  Just (instantiateTerm value (abstractOver pattern result))
refineType (S fuel) NatZero value result fallback =
  Just (NatCase (Lambda Erased NatType (Universe 0)) value result
    (Lambda Linear NatType (weaken fallback)))
refineType (S fuel) (NatSucc rest) value result fallback = do
  let next = instantiateTerm (Variable FZ) (abstractOver (weaken rest) (weaken result))
  Just (NatCase (Lambda Erased NatType (Universe 0)) value fallback (Lambda Linear NatType next))
refineType _ _ _ _ _ = Nothing

-- General variable-index abstraction supports dependent telescopes. Constants
-- are kept fixed here; the Nat-pattern rule below supplies a decision motive.
public export
abstractFamilyMotive : Nat -> List (Term n) -> Term n -> Term n -> Term n -> Maybe (Term n)
abstractFamilyMotive Z [] indices family result = Just (Lambda Erased family (weaken result))
abstractFamilyMotive (S count) (actual :: remaining) (Pi Erased domain body) family result = do
  let refined = case actual of
        Variable _ => abstractOver actual result
        _ => weaken result
  next <- abstractFamilyMotive count (map weaken remaining) body
    (Apply (weaken family) (Variable FZ)) refined
  Just (Lambda Erased domain next)
abstractFamilyMotive _ _ _ _ _ = Nothing

public export
natFamilyMotive : Term n -> Term n -> Term n -> Term n -> Maybe (Term n)
natFamilyMotive actual (Pi Erased NatType (Universe 0)) family result =
  if not (natPattern 16 actual) then Nothing else do
    let generic : Term (S (S n)) = Variable (FS FZ)
    body <- refineType 16 (weaken (weaken actual)) generic (weaken (weaken result))
      (Apply (weaken (weaken family)) generic)
    Just (Lambda Erased NatType (Lambda Erased (Apply (weaken family) (Variable FZ)) body))
natFamilyMotive _ _ _ _ = Nothing

natDisjoint : Nat -> Term n -> Term n -> Bool
natDisjoint Z _ _ = False
natDisjoint (S fuel) NatZero (NatSucc _) = True
natDisjoint (S fuel) (NatSucc _) NatZero = True
natDisjoint _ _ _ = False

constructorDisjoint : GlobalContext -> Nat -> Nat -> Term n -> Term n -> Bool
constructorDisjoint globals Z count chain actual = False
constructorDisjoint globals (S fuel) count (Pi _ _ body) actual = constructorDisjoint globals fuel count body (weaken actual)
constructorDisjoint globals (S fuel) count result actual = case dataTypeSpine result of
  Just (_, args) => case drop count args of
    [index] => case (normalizeGlobals (globalValue globals) 64 index, normalizeGlobals (globalValue globals) 64 actual) of
      (Normal left, Normal right) => natDisjoint fuel left right
      _ => False
    _ => False
  Nothing => False

identityBranch : Nat -> Term n -> Term n -> Maybe (Term n)
identityBranch Z chain built = Nothing
identityBranch (S fuel) (Pi q domain body) built =
  map (Lambda q domain) (identityBranch fuel body (Apply (weaken built) (Variable FZ)))
identityBranch (S fuel) _ built = Just built

public export
missingIndexBranch : GlobalContext -> DataDecl -> Nat -> List (Term n) -> Maybe (Term n)
missingIndexBranch globals decl tag actuals = do
  [actual] <- Just (drop (parameterCount decl) actuals) | _ => Nothing
  closed <- constructorType decl tag
  let parameterArgs = take (parameterCount decl) actuals
  Right chain <- Just (instantiateParameters parameterArgs (rename absurd closed)) | _ => Nothing
  if constructorDisjoint globals 64 (parameterCount decl) chain actual
    then identityBranch 64 chain (applyAll (DataCon decl.key tag (parameterCount decl)) parameterArgs)
    else Nothing
