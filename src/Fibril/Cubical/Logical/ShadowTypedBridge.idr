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

||| Select the actual endpoint constructor, since equal declared endpoints can
||| admit either constructor under different faces.
public export
data LeftEndpointWitness : {0 context : Vect n LogicalType} ->
  {0 l, r : LogicalVar context a} -> {0 face : ScopedFace d} -> {0 i : ScopedInterval d} ->
  DeclaredEndpoint (DeclarePath (LRef l) (LRef r) NoPaths) face
    (NeutralAt LHere i) (Embed (LRef l)) -> Type where
  IsDeclaredLeft : {0 context : Vect n LogicalType} -> {0 a : LogicalType} ->
    {0 l, r : LogicalVar context a} -> {face : ScopedFace d} -> {i : ScopedInterval d} ->
    (check : boundedEndpointEntails face i False = True) ->
    LeftEndpointWitness {l} {r} {face} {i} (DeclaredLeft {face} {i} DeclaredHere check)

public export
data RightEndpointWitness : {0 context : Vect n LogicalType} ->
  {0 l, r : LogicalVar context a} -> {0 face : ScopedFace d} -> {0 i : ScopedInterval d} ->
  DeclaredEndpoint (DeclarePath (LRef l) (LRef r) NoPaths) face
    (NeutralAt LHere i) (Embed (LRef r)) -> Type where
  IsDeclaredRight : {0 context : Vect n LogicalType} -> {0 a : LogicalType} ->
    {0 l, r : LogicalVar context a} -> {face : ScopedFace d} -> {i : ScopedInterval d} ->
    (check : boundedEndpointEntails face i True = True) ->
    RightEndpointWitness {l} {r} {face} {i} (DeclaredRight {face} {i} DeclaredHere check)

||| Translate a source endpoint of the selected constructor.
public export
bridgeLeft : {n, d : Nat} -> {0 context : Vect n LogicalType} ->
  (l, r : LogicalVar context a) -> (face : ScopedFace d) -> (i : ScopedInterval d) ->
  (source : DeclaredEndpoint (DeclarePath (LRef l) (LRef r) NoPaths) face
    (NeutralAt LHere i) (Embed (LRef l))) ->
  LeftEndpointWitness source ->
  NeutralEqual (bridgeContext l r) face (NApply (NPath FZ) i) (NBase (variableIndex l)) NType
bridgeLeft l r face i _ (IsDeclaredLeft check) =
  NEndpointLeft (NPathVar FZ) (NBaseVar (variableIndex l)) (endpointEntailsFace face i False check)

public export
bridgeRight : {n, d : Nat} -> {0 context : Vect n LogicalType} ->
  (l, r : LogicalVar context a) -> (face : ScopedFace d) -> (i : ScopedInterval d) ->
  (source : DeclaredEndpoint (DeclarePath (LRef l) (LRef r) NoPaths) face
    (NeutralAt LHere i) (Embed (LRef r))) ->
  RightEndpointWitness source ->
  NeutralEqual (bridgeContext l r) face (NApply (NPath FZ) i) (NBase (variableIndex r)) NType
bridgeRight l r face i _ (IsDeclaredRight check) =
  NEndpointRight (NPathVar FZ) (NBaseVar (variableIndex r)) (endpointEntailsFace face i True check)

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
||| Target checks are derived from the selected source endpoint rules.
public export
bridgeDeclaredPath : {n, d : Nat} -> {0 context : Vect n LogicalType} ->
  (l, r : LogicalVar context a) -> (face : ScopedFace d) ->
  {0 path : DeclaredShadowPath (DeclarePath (LRef l) (LRef r) NoPaths) face
    (Embed (LRef l)) (Embed (LRef r))} ->
  NeutralShadowWitness l r face path ->
  NeutralHasType (bridgeContext l r) face (NAbstract (NApply (NPath FZ) (Var FZ)))
    (NPathType NType (NBase (variableIndex l)) (NBase (variableIndex r)))
bridgeDeclaredPath l r face (WitnessNeutral zero one) =
  NIntro NBaseForm (NBaseVar (variableIndex l)) (NBaseVar (variableIndex r))
    (NElim (NPathVar FZ) (Var FZ))
    (bridgeLeft l r _ _ (DeclaredLeft DeclaredHere zero) (IsDeclaredLeft zero))
    (bridgeRight l r _ _ (DeclaredRight DeclaredHere one) (IsDeclaredRight one))

||| The interpretation relation is indexed by the actual source body and target
||| expression. Only base variables and the single declared neutral are admitted.
public export
data BridgeableBody : {0 context : Vect n LogicalType} ->
  PathBody context [a] d a -> NeutralExpr n 1 d -> Type where
  BridgeVariable : (v : LogicalVar context a) ->
    BridgeableBody (Embed (LRef v)) (NBase (variableIndex v))
  BridgeNeutral : {0 context : Vect n LogicalType} -> {0 a : LogicalType} -> (i : ScopedInterval d) ->
    BridgeableBody {context} (NeutralAt LHere i) (NApply (NPath FZ) i)

public export
bridgeBodyType : {0 context : Vect n LogicalType} ->
  (l, r : LogicalVar context a) -> (face : ScopedFace d) ->
  {0 body : PathBody context [a] d a} -> {0 target : NeutralExpr n 1 d} ->
  BridgeableBody {context} body target ->
  NeutralHasType (bridgeContext l r) face target NType
bridgeBodyType l r face (BridgeVariable v) = NBaseVar (variableIndex v)
bridgeBodyType l r face (BridgeNeutral i) = NElim (NPathVar FZ) i

||| Certificates select bridgeable proof constructors and matching target terms.
public export
data BridgeableEquality : {0 context : Vect n LogicalType} ->
  {0 l, r : LogicalVar context a} -> {0 face : ScopedFace d} ->
  {0 x, y : PathBody context [a] d a} ->
  (source : BodyEqual (DeclarePath (LRef l) (LRef r) NoPaths) face x y) ->
  NeutralExpr n 1 d -> NeutralExpr n 1 d -> Type where
  BridgeRefl : BridgeableBody x tx -> BridgeableEquality {l} {r} (BodyRefl {x}) tx tx
  BridgeSym : BridgeableEquality eq tx ty -> BridgeableEquality (BodySym eq) ty tx
  BridgeTrans : {0 context : Vect n LogicalType} -> {0 a : LogicalType} ->
    {0 l, r : LogicalVar context a} -> {0 face : ScopedFace d} ->
    {0 x, y, z : PathBody context [a] d a} ->
    {0 eq1 : BodyEqual (DeclarePath (LRef l) (LRef r) NoPaths) face x y} ->
    {0 eq2 : BodyEqual (DeclarePath (LRef l) (LRef r) NoPaths) face y z} ->
    BridgeableEquality eq1 tx ty -> BridgeableEquality eq2 ty tz ->
    BridgeableEquality (BodyTrans eq1 eq2) tx tz
  BridgeRestrict : {0 context : Vect n LogicalType} -> {0 a : LogicalType} ->
    {0 l, r : LogicalVar context a} -> {0 face : ScopedFace d} ->
    {source : ScopedFace d} -> {check : boundedFaceEntails face source = True} ->
    {0 x, y : PathBody context [a] d a} ->
    {0 eq : BodyEqual (DeclarePath (LRef l) (LRef r) NoPaths) source x y} ->
    BridgeableEquality {context} {l} {r} eq tx ty ->
    BridgeableEquality (BodyRestrict {face} {source} eq check) tx ty
  BridgeTransRefl : BridgeableEquality eq tx ty ->
    BridgeableEquality (BodyTrans eq BodyRefl) tx ty
  BridgeLeftReflTrans : BridgeableEquality eq tx ty ->
    BridgeableEquality (BodyTrans BodyRefl eq) tx ty
  BridgeRestrictRefl : {0 context : Vect n LogicalType} -> {0 a : LogicalType} ->
    {0 l, r : LogicalVar context a} -> {0 face : ScopedFace d} ->
    {0 x : PathBody context [a] d a} -> {0 tx : NeutralExpr n 1 d} -> {source : ScopedFace d} ->
    {check : boundedFaceEntails face source = True} -> BridgeableBody {context} x tx ->
    BridgeableEquality {l} {r} (BodyRestrict {face} {source} (BodyRefl {x}) check) tx tx
  BridgeRestrictLeft : {0 context : Vect n LogicalType} -> {0 a : LogicalType} ->
    {0 l, r : LogicalVar context a} -> {0 face : ScopedFace d} ->
    {source : ScopedFace d} -> {i : ScopedInterval d} ->
    {original : boundedEndpointEntails source i False = True} ->
    {restriction : boundedFaceEntails face source = True} ->
    (rechecked : boundedEndpointEntails face i False = True) ->
    BridgeableEquality {context} {l} {r}
      (BodyRestrict {face} {source} (BodyEndpoint (DeclaredLeft {face = source} {i} DeclaredHere original)) restriction)
      (NApply (NPath FZ) i) (NBase (variableIndex l))
  BridgeRestrictRight : {0 context : Vect n LogicalType} -> {0 a : LogicalType} ->
    {0 l, r : LogicalVar context a} -> {0 face : ScopedFace d} ->
    {source : ScopedFace d} -> {i : ScopedInterval d} ->
    {original : boundedEndpointEntails source i True = True} ->
    {restriction : boundedFaceEntails face source = True} ->
    (rechecked : boundedEndpointEntails face i True = True) ->
    BridgeableEquality {context} {l} {r}
      (BodyRestrict {face} {source} (BodyEndpoint (DeclaredRight {face = source} {i} DeclaredHere original)) restriction)
      (NApply (NPath FZ) i) (NBase (variableIndex r))
  BridgeEndpointLeft : {0 context : Vect n LogicalType} -> {0 a : LogicalType} ->
    {0 l, r : LogicalVar context a} -> {0 face : ScopedFace d} -> {i : ScopedInterval d} ->
    {check : boundedEndpointEntails face i False = True} ->
    BridgeableEquality {context} {l} {r} (BodyEndpoint (DeclaredLeft {face} {i} DeclaredHere check))
      (NApply (NPath FZ) i) (NBase (variableIndex l))
  BridgeEndpointRight : {0 context : Vect n LogicalType} -> {0 a : LogicalType} ->
    {0 l, r : LogicalVar context a} -> {0 face : ScopedFace d} -> {i : ScopedInterval d} ->
    {check : boundedEndpointEntails face i True = True} ->
    BridgeableEquality {context} {l} {r} (BodyEndpoint (DeclaredRight {face} {i} DeclaredHere check))
      (NApply (NPath FZ) i) (NBase (variableIndex r))

public export
bridgeEquality : {0 context : Vect n LogicalType} ->
  (l, r : LogicalVar context a) -> (face : ScopedFace d) ->
  {0 x, y : PathBody context [a] d a} ->
  {0 source : BodyEqual (DeclarePath (LRef l) (LRef r) NoPaths) face x y} ->
  BridgeableEquality source tx ty -> NeutralEqual (bridgeContext l r) face tx ty NType
bridgeEquality l r face (BridgeRefl body) = NRefl (bridgeBodyType l r face body)
bridgeEquality l r face (BridgeSym eq) = NSym (bridgeEquality l r face eq)
bridgeEquality l r face (BridgeTrans eq1 eq2) =
  NTrans (bridgeEquality l r face eq1) (bridgeEquality l r face eq2)
bridgeEquality l r face (BridgeRestrict {source} {check} eq) =
  NEqualRestrict (bridgeEquality l r source eq) check
bridgeEquality l r face (BridgeTransRefl eq) = bridgeEquality l r face eq
bridgeEquality l r face (BridgeLeftReflTrans eq) = bridgeEquality l r face eq
bridgeEquality l r face (BridgeRestrictRefl body) = NRefl (bridgeBodyType l r face body)
bridgeEquality l r face (BridgeRestrictLeft {i} check) =
  NEndpointLeft (NPathVar FZ) (NBaseVar (variableIndex l)) (endpointEntailsFace face i False check)
bridgeEquality l r face (BridgeRestrictRight {i} check) =
  NEndpointRight (NPathVar FZ) (NBaseVar (variableIndex r)) (endpointEntailsFace face i True check)
bridgeEquality l r face (BridgeEndpointLeft {i} {check}) =
  NEndpointLeft (NPathVar FZ) (NBaseVar (variableIndex l)) (endpointEntailsFace face i False check)
bridgeEquality l r face (BridgeEndpointRight {i} {check}) =
  NEndpointRight (NPathVar FZ) (NBaseVar (variableIndex r)) (endpointEntailsFace face i True check)

||| Translate the actual two boundary proofs of a neutral abstraction.
public export
bridgeAbstract : {0 context : Vect n LogicalType} ->
  (l, r : LogicalVar context a) -> (face : ScopedFace d) ->
  {0 zero : BodyEqual (DeclarePath (LRef l) (LRef r) NoPaths)
    (SConjunction (weakenFace face) (SEndpoint FZ False))
    (NeutralAt LHere (Var FZ)) (Embed (LRef l))} ->
  {0 one : BodyEqual (DeclarePath (LRef l) (LRef r) NoPaths)
    (SConjunction (weakenFace face) (SEndpoint FZ True))
    (NeutralAt LHere (Var FZ)) (Embed (LRef r))} ->
  BridgeableEquality zero (NApply (NPath FZ) (Var FZ)) (NBase (variableIndex l)) ->
  BridgeableEquality one (NApply (NPath FZ) (Var FZ)) (NBase (variableIndex r)) ->
  NeutralHasType (bridgeContext l r) face (NAbstract (NApply (NPath FZ) (Var FZ)))
    (NPathType NType (NBase (variableIndex l)) (NBase (variableIndex r)))
bridgeAbstract l r face zero one =
  NIntro NBaseForm (NBaseVar (variableIndex l)) (NBaseVar (variableIndex r))
    (NElim (NPathVar FZ) (Var FZ))
    (bridgeEquality l r _ zero) (bridgeEquality l r _ one)
