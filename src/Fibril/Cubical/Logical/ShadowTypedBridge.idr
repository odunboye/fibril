module Fibril.Cubical.Logical.ShadowTypedBridge

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

||| Variables retain their context positions; all source types are interpreted
||| as the single abstract base of NeutralExpr, not as their logical meaning.
public export
variableIndex : {0 context : Vect n LogicalType} -> LogicalVar context a -> Fin n
variableIndex LHere = FZ
variableIndex (LThere v) = FS (variableIndex v)

||| The common fragment has one declared path with variable endpoints.
public export
bridgeContext : {0 context : Vect n LogicalType} -> LogicalVar context a -> LogicalVar context a -> PathContext n 1
bridgeContext l r = [PathBetween (variableIndex l) (variableIndex r)]

||| Translate a source left endpoint derivation, independently checking the
||| target's bounded syntactic entailment after the source interval preflight.
public export
bridgeLeft : {n, d : Nat} -> {0 context : Vect n LogicalType} ->
  (l, r : LogicalVar context a) -> (face : ScopedFace d) -> (i : ScopedInterval d) ->
  DeclaredEndpoint (DeclarePath (LRef l) (LRef r) NoPaths) face
    (NeutralAt LHere i) (Embed (LRef l)) ->
  TypedPath.boundedFaceEntails face (scopedEndpoint i False) = True ->
  NeutralEqual (bridgeContext l r) face (NApply (NPath FZ) i) (NBase (variableIndex l)) NType
bridgeLeft l r face i source check = NEndpointLeft (NPathVar FZ) (NBaseVar (variableIndex l)) check

public export
bridgeRight : {n, d : Nat} -> {0 context : Vect n LogicalType} ->
  (l, r : LogicalVar context a) -> (face : ScopedFace d) -> (i : ScopedInterval d) ->
  DeclaredEndpoint (DeclarePath (LRef l) (LRef r) NoPaths) face
    (NeutralAt LHere i) (Embed (LRef r)) ->
  TypedPath.boundedFaceEntails face (scopedEndpoint i True) = True ->
  NeutralEqual (bridgeContext l r) face (NApply (NPath FZ) i) (NBase (variableIndex r)) NType
bridgeRight l r face i source check = NEndpointRight (NPathVar FZ) (NBaseVar (variableIndex r)) check

||| Evidence selects exactly the neutral abstraction and its endpoint rules;
||| arbitrary BodyEqual derivations are outside this bridge.
public export
data NeutralShadowWitness : {n, d : Nat} -> {0 context : Vect n LogicalType} ->
  (l, r : LogicalVar context a) -> (face : ScopedFace d) ->
  DeclaredShadowPath (DeclarePath (LRef l) (LRef r) NoPaths) face
    (Embed (LRef l)) (Embed (LRef r)) -> Type where
  WitnessNeutral : {0 context : Vect n LogicalType} -> {0 a : LogicalType} ->
    {0 l, r : LogicalVar context a} -> {0 face : ScopedFace d} ->
    (zero : Fibril.Cubical.Logical.ShadowPath.boundedEndpointEntails
      (SConjunction (weakenFace face) (SEndpoint FZ False)) (Var FZ) False = True) ->
    (one : Fibril.Cubical.Logical.ShadowPath.boundedEndpointEntails
      (SConjunction (weakenFace face) (SEndpoint FZ True)) (Var FZ) True = True) ->
    NeutralShadowWitness l r face
      (ShadowAbstract (NeutralAt LHere (Var FZ))
        (BodyEndpoint (DeclaredLeft DeclaredHere zero))
        (BodyEndpoint (DeclaredRight DeclaredHere one)))

||| A nonconstant abstraction is derived from the source's endpoint checks.
||| The extra checks are target entailment, not target typing assumptions.
public export
bridgeDeclaredPath : {n, d : Nat} -> {0 context : Vect n LogicalType} ->
  (l, r : LogicalVar context a) -> (face : ScopedFace d) ->
  {0 path : DeclaredShadowPath (DeclarePath (LRef l) (LRef r) NoPaths) face
    (Embed (LRef l)) (Embed (LRef r))} ->
  NeutralShadowWitness l r face path ->
  TypedPath.boundedFaceEntails (SConjunction (weakenFace face) (SEndpoint FZ False)) (SEndpoint FZ False) = True ->
  TypedPath.boundedFaceEntails (SConjunction (weakenFace face) (SEndpoint FZ True)) (SEndpoint FZ True) = True ->
  NeutralHasType (bridgeContext l r) face (NAbstract (NApply (NPath FZ) (Var FZ)))
    (NPathType NType (NBase (variableIndex l)) (NBase (variableIndex r)))
bridgeDeclaredPath l r face (WitnessNeutral zero one) targetZero targetOne =
  NIntro NBaseForm (NBaseVar (variableIndex l)) (NBaseVar (variableIndex r))
    (NElim (NPathVar FZ) (Var FZ))
    (bridgeLeft l r _ _ (DeclaredLeft DeclaredHere zero) targetZero)
    (bridgeRight l r _ _ (DeclaredRight DeclaredHere one) targetOne)
