module Fibril.Cubical.Logical.ShadowPath

import Decidable.Equality
import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.ScopedSyntax

import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

||| Pure shadow terms embed as dimension-independent terms. Neutral path names
||| have a separately scoped context of underlying logical types.
public export
data PathBody : (0 context : Vect n LogicalType) -> (0 paths : Vect k LogicalType) -> Nat -> (0 ty : LogicalType) -> Type where
  Embed : LogicalTerm context a -> PathBody context paths d a
  NeutralAt : LogicalVar paths a -> ScopedInterval d -> PathBody context paths d a
  BodyLam : PathBody (a :: context) paths d b -> PathBody context paths d (LArrow a b)
  BodyApp : PathBody context paths d (LArrow a b) -> PathBody context paths d a -> PathBody context paths d b
  BodyUnitElim : PathBody context paths d LUnit -> PathBody context paths d a -> PathBody context paths d a
  BodyIf : PathBody context paths d LBool -> PathBody context paths d a -> PathBody context paths d a -> PathBody context paths d a

public export
mapPathDimensions : (Fin d -> ScopedInterval e) -> PathBody context paths d a -> PathBody context paths e a
mapPathDimensions env (Embed t) = Embed t
mapPathDimensions env (NeutralAt p i) = NeutralAt p (substituteScoped env i)
mapPathDimensions env (BodyLam b) = BodyLam (mapPathDimensions env b)
mapPathDimensions env (BodyApp f x) = BodyApp (mapPathDimensions env f) (mapPathDimensions env x)
mapPathDimensions env (BodyUnitElim x b) = BodyUnitElim (mapPathDimensions env x) (mapPathDimensions env b)
mapPathDimensions env (BodyIf c t f) = BodyIf (mapPathDimensions env c) (mapPathDimensions env t) (mapPathDimensions env f)

public export
mapPathTerms : LogicalSubstitution context target -> PathBody context paths d a -> PathBody target paths d a
mapPathTerms sigma (Embed t) = Embed (substituteLogical sigma t)
mapPathTerms sigma (NeutralAt p i) = NeutralAt p i
mapPathTerms sigma (BodyLam b) = BodyLam (mapPathTerms (liftLogicalSubstitution sigma) b)
mapPathTerms sigma (BodyApp f x) = BodyApp (mapPathTerms sigma f) (mapPathTerms sigma x)
mapPathTerms sigma (BodyUnitElim x b) = BodyUnitElim (mapPathTerms sigma x) (mapPathTerms sigma b)
mapPathTerms sigma (BodyIf c t f) = BodyIf (mapPathTerms sigma c) (mapPathTerms sigma t) (mapPathTerms sigma f)

||| Term substitution and dimension substitution operate on disjoint scopes.
public export
pathMixedSubstitution : (sigma : LogicalSubstitution context target) -> (dims : Fin d -> ScopedInterval e) ->
  (body : PathBody context paths d a) ->
  mapPathDimensions dims (mapPathTerms sigma body) = mapPathTerms sigma (mapPathDimensions dims body)
pathMixedSubstitution sigma dims (Embed t) = Refl
pathMixedSubstitution sigma dims (NeutralAt p i) = Refl
pathMixedSubstitution sigma dims (BodyLam b) = cong BodyLam (pathMixedSubstitution (liftLogicalSubstitution sigma) dims b)
pathMixedSubstitution sigma dims (BodyApp f x) = cong2 BodyApp (pathMixedSubstitution sigma dims f) (pathMixedSubstitution sigma dims x)
pathMixedSubstitution sigma dims (BodyUnitElim x b) = cong2 BodyUnitElim (pathMixedSubstitution sigma dims x) (pathMixedSubstitution sigma dims b)
pathMixedSubstitution sigma dims (BodyIf c t f) = rewrite pathMixedSubstitution sigma dims c in rewrite pathMixedSubstitution sigma dims t in rewrite pathMixedSubstitution sigma dims f in Refl

public export
atDimension : ScopedInterval d -> Fin (S d) -> ScopedInterval d
atDimension r FZ = r
atDimension r (FS i) = Var i

intervalIdentity : (i : ScopedInterval d) -> substituteScoped Var i = i
intervalIdentity Zero = Refl
intervalIdentity One = Refl
intervalIdentity (Var i) = Refl
intervalIdentity (Meet x y) = cong2 Meet (intervalIdentity x) (intervalIdentity y)
intervalIdentity (Join x y) = cong2 Join (intervalIdentity x) (intervalIdentity y)
intervalIdentity (Reverse x) = cong Reverse (intervalIdentity x)

intervalRestored : (side : ScopedInterval d) -> (i : ScopedInterval d) ->
  substituteScoped (atDimension side) (substituteScoped (Var . FS) i) = i
intervalRestored side i =
  trans (intervalSubstitutionComposition (Var . FS) (atDimension side) i)
    (intervalIdentity i)

||| Instantiation cancels dimension weakening for every typed body, including
||| logical binders; the chosen replacement need not itself be an endpoint.
public export
pathDimensionsRestored : (side : ScopedInterval d) -> (body : PathBody context paths d a) ->
  mapPathDimensions (atDimension side) (mapPathDimensions (Var . FS) body) = body
pathDimensionsRestored side (Embed t) = Refl
pathDimensionsRestored side (NeutralAt p i) = cong (NeutralAt p) (intervalRestored side i)
pathDimensionsRestored side (BodyLam b) = cong BodyLam (pathDimensionsRestored side b)
pathDimensionsRestored side (BodyApp f x) = cong2 BodyApp (pathDimensionsRestored side f) (pathDimensionsRestored side x)
pathDimensionsRestored side (BodyUnitElim x b) = cong2 BodyUnitElim (pathDimensionsRestored side x) (pathDimensionsRestored side b)
pathDimensionsRestored side (BodyIf c t f) = rewrite pathDimensionsRestored side c in rewrite pathDimensionsRestored side t in rewrite pathDimensionsRestored side f in Refl

||| Path abstraction requires literal, typed endpoint equalities. It provides no
||| face conversion or equations for neutral path names.
public export
data ExactPath : {0 context : Vect n LogicalType} -> {0 paths : Vect k LogicalType} ->
  {0 d : Nat} -> {0 a : LogicalType} -> PathBody context paths d a -> PathBody context paths d a -> Type where
  PathAbstract : (body : PathBody context paths (S d) a) ->
    mapPathDimensions (atDimension Zero) body = left ->
    mapPathDimensions (atDimension One) body = right ->
    ExactPath left right

||| Application computes by dimension substitution in the checked body.
public export
applyExactPath : ExactPath {context} {paths} {d} {a} left right -> ScopedInterval d -> PathBody context paths d a
applyExactPath (PathAbstract body _ _) r = mapPathDimensions (atDimension r) body

public export
pathAtZero : (p : ExactPath left right) -> applyExactPath p Zero = left
pathAtZero (PathAbstract body zero one) = zero

public export
pathAtOne : (p : ExactPath left right) -> applyExactPath p One = right
pathAtOne (PathAbstract body zero one) = one

public export
substituteExactPath : {0 context : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  {0 paths : Vect k LogicalType} -> {0 d : Nat} -> {0 a : LogicalType} ->
  {0 left, right : PathBody context paths d a} -> (sigma : LogicalSubstitution context target) ->
  ExactPath {context} {paths} {d} {a} left right ->
  ExactPath (mapPathTerms sigma left) (mapPathTerms sigma right)
substituteExactPath sigma (PathAbstract body zero one) =
  PathAbstract (mapPathTerms sigma body)
    (trans (pathMixedSubstitution sigma (atDimension Zero) body) (cong (mapPathTerms sigma) zero))
    (trans (pathMixedSubstitution sigma (atDimension One) body) (cong (mapPathTerms sigma) one))

public export
substitutePathApplication : {0 context : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  {0 paths : Vect k LogicalType} -> {0 d : Nat} -> {0 a : LogicalType} ->
  {0 left, right : PathBody context paths d a} -> (sigma : LogicalSubstitution context target) ->
  (p : ExactPath {context} {paths} {d} {a} left right) -> (r : ScopedInterval d) ->
  applyExactPath (substituteExactPath sigma p) r = mapPathTerms sigma (applyExactPath p r)
substitutePathApplication sigma (PathAbstract body zero one) r = pathMixedSubstitution sigma (atDimension r) body

||| Endpoints are ordinary typed terms in the entire term context, and cannot
||| mention path names. Declarations are independent of dimension variables.
public export
data PathDeclarations : Vect n LogicalType -> Vect k LogicalType -> Type where
  NoPaths : PathDeclarations context []
  DeclarePath : LogicalTerm context a -> LogicalTerm context a ->
    PathDeclarations context paths -> PathDeclarations context (a :: paths)

public export
data DeclaredPath : PathDeclarations context paths -> LogicalVar paths a ->
                    LogicalTerm context a -> LogicalTerm context a -> Type where
  DeclaredHere : DeclaredPath (DeclarePath left right rest) LHere left right
  DeclaredThere : DeclaredPath rest p left right ->
    DeclaredPath (DeclarePath l r rest) (LThere p) left right

public export
substitutePathDeclarations : LogicalSubstitution context target ->
  PathDeclarations context paths -> PathDeclarations target paths
substitutePathDeclarations sigma NoPaths = NoPaths
substitutePathDeclarations sigma (DeclarePath l r rest) =
  DeclarePath (substituteLogical sigma l) (substituteLogical sigma r)
    (substitutePathDeclarations sigma rest)

public export
substituteDeclaredPath : {0 context : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  {0 paths : Vect k LogicalType} -> {0 a : LogicalType} ->
  {0 declarations : PathDeclarations context paths} ->
  {0 p : LogicalVar paths a} -> {0 left, right : LogicalTerm context a} -> (sigma : LogicalSubstitution context target) ->
  DeclaredPath declarations p left right ->
  DeclaredPath (substitutePathDeclarations sigma declarations) p
    (substituteLogical sigma left) (substituteLogical sigma right)
substituteDeclaredPath sigma DeclaredHere = DeclaredHere
substituteDeclaredPath sigma (DeclaredThere p) = DeclaredThere (substituteDeclaredPath sigma p)

||| Preflight the interval before extracting its endpoint face. A False result
||| includes exhaustion and is not a proof that entailment fails. This bounds
||| the admitted interval and face input sizes, not all evaluation work.
public export
boundedEndpointEntails : {d : Nat} -> ScopedFace d -> ScopedInterval d -> Bool -> Bool
boundedEndpointEntails face i endpoint =
  case intervalNodes 12 i of
    Nothing => False
    Just _ => boundedFaceEntails face (scopedEndpoint i endpoint)

||| Acceptance after interval preflight entails acceptance by the face solver.
public export
endpointEntailsFace : (face : ScopedFace d) -> (i : ScopedInterval d) -> (side : Bool) ->
  boundedEndpointEntails face i side = True ->
  boundedFaceEntails face (scopedEndpoint i side) = True
endpointEntailsFace face i side evidence with (intervalNodes 12 i)
  endpointEntailsFace face i side Refl | Nothing impossible
  endpointEntailsFace face i side evidence | Just _ = evidence

||| A declarative endpoint equation, valid only under the displayed face.
||| This is not runtime equality or a quantitative resource theorem.
public export
data DeclaredEndpoint : PathDeclarations context paths -> ScopedFace d ->
  PathBody context paths d a -> PathBody context paths d a -> Type where
  DeclaredLeft : {0 context : Vect n LogicalType} -> {0 paths : Vect k LogicalType} -> {0 declarations : PathDeclarations context paths} -> {0 face : ScopedFace d} -> {0 p : LogicalVar paths a} -> {0 left, right : LogicalTerm context a} -> {i : ScopedInterval d} -> DeclaredPath declarations p left right ->
    boundedEndpointEntails face i False = True ->
    DeclaredEndpoint declarations face (NeutralAt p i) (Embed left)
  DeclaredRight : {0 context : Vect n LogicalType} -> {0 paths : Vect k LogicalType} -> {0 declarations : PathDeclarations context paths} -> {0 face : ScopedFace d} -> {0 p : LogicalVar paths a} -> {0 left, right : LogicalTerm context a} -> {i : ScopedInterval d} -> DeclaredPath declarations p left right ->
    boundedEndpointEntails face i True = True ->
    DeclaredEndpoint declarations face (NeutralAt p i) (Embed right)

public export
substituteDeclaredEndpoint : {0 context : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  {0 paths : Vect k LogicalType} -> {0 a : LogicalType} -> {0 d : Nat} ->
  {0 declarations : PathDeclarations context paths} -> {0 face : ScopedFace d} ->
  {0 x, y : PathBody context paths d a} -> (sigma : LogicalSubstitution context target) ->
  DeclaredEndpoint declarations face x y ->
  DeclaredEndpoint (substitutePathDeclarations sigma declarations) face
    (mapPathTerms sigma x) (mapPathTerms sigma y)
substituteDeclaredEndpoint sigma (DeclaredLeft p entails) = DeclaredLeft (substituteDeclaredPath sigma p) entails
substituteDeclaredEndpoint sigma (DeclaredRight p entails) = DeclaredRight (substituteDeclaredPath sigma p) entails

||| ExactPath application may be used at a declared neutral endpoint only when
||| its computed body is literally that neutral application.
public export
declaredExactApplicationLeft : (path : ExactPath {context} {paths} {d} {a} x y) ->
  (i : ScopedInterval d) -> (p : LogicalVar paths a) ->
  applyExactPath path i = NeutralAt p i ->
  DeclaredPath declarations p left right ->
  boundedEndpointEntails face i False = True ->
  DeclaredEndpoint declarations face (applyExactPath path i) (Embed left)
declaredExactApplicationLeft path i p eq declared entails =
  rewrite eq in DeclaredLeft declared entails

||| Declarative equality is indexed by the exact declarations and restriction.
||| There is deliberately no rule reflecting it into Idris or logical equality.
public export
data BodyEqual : PathDeclarations context paths -> ScopedFace d ->
                 PathBody context paths d a -> PathBody context paths d a -> Type where
  BodyRefl : BodyEqual declarations face x x
  BodySym : BodyEqual declarations face x y -> BodyEqual declarations face y x
  BodyTrans : BodyEqual declarations face x y -> BodyEqual declarations face y z ->
              BodyEqual declarations face x z
  BodyEndpoint : DeclaredEndpoint declarations face x y -> BodyEqual declarations face x y
  BodyRestrict : {0 context : Vect n LogicalType} -> {0 paths : Vect k LogicalType} -> {0 declarations : PathDeclarations context paths} -> {0 face : ScopedFace d} -> {0 x, y : PathBody context paths d a} -> {source : ScopedFace d} -> BodyEqual declarations source x y ->
    boundedFaceEntails face source = True -> BodyEqual declarations face x y
  BodyAppEqual : BodyEqual declarations face f g -> BodyEqual declarations face x y ->
    BodyEqual declarations face (BodyApp f x) (BodyApp g y)
  BodyIfEqual : BodyEqual declarations face c c' -> BodyEqual declarations face t t' ->
    BodyEqual declarations face f f' -> BodyEqual declarations face (BodyIf c t f) (BodyIf c' t' f')
  BodyUnitElimEqual : BodyEqual declarations face x y -> BodyEqual declarations face b b' ->
    BodyEqual declarations face (BodyUnitElim x b) (BodyUnitElim y b')

public export
substituteBodyEqual : {0 context : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  {0 paths : Vect k LogicalType} -> {0 d : Nat} -> {0 a : LogicalType} ->
  {0 declarations : PathDeclarations context paths} -> {0 face : ScopedFace d} ->
  {0 x, y : PathBody context paths d a} -> (sigma : LogicalSubstitution context target) ->
  BodyEqual declarations face x y -> BodyEqual (substitutePathDeclarations sigma declarations) face
    (mapPathTerms sigma x) (mapPathTerms sigma y)
substituteBodyEqual sigma BodyRefl = BodyRefl
substituteBodyEqual sigma (BodySym eq) = BodySym (substituteBodyEqual sigma eq)
substituteBodyEqual sigma (BodyTrans x y) = BodyTrans (substituteBodyEqual sigma x) (substituteBodyEqual sigma y)
substituteBodyEqual sigma (BodyEndpoint eq) = BodyEndpoint (substituteDeclaredEndpoint sigma eq)
substituteBodyEqual sigma (BodyRestrict eq entails) = BodyRestrict (substituteBodyEqual sigma eq) entails
substituteBodyEqual sigma (BodyAppEqual f x) = BodyAppEqual (substituteBodyEqual sigma f) (substituteBodyEqual sigma x)
substituteBodyEqual sigma (BodyIfEqual c t f) = BodyIfEqual (substituteBodyEqual sigma c) (substituteBodyEqual sigma t) (substituteBodyEqual sigma f)
substituteBodyEqual sigma (BodyUnitElimEqual x b) = BodyUnitElimEqual (substituteBodyEqual sigma x) (substituteBodyEqual sigma b)

||| Recertify only the bounded checks actually used in an equality derivation.
public export
data DimensionEvidence : {0 context : Vect n LogicalType} -> {0 paths : Vect k LogicalType} ->
  {0 declarations : PathDeclarations context paths} -> {0 face : ScopedFace d} ->
  {0 x, y : PathBody context paths d a} -> (env : Fin d -> ScopedInterval e) -> (target : ScopedFace e) ->
  BodyEqual declarations face x y -> Type where
  DimRefl : DimensionEvidence env target BodyRefl
  DimSym : DimensionEvidence env target eq -> DimensionEvidence env target (BodySym eq)
  DimTrans : {0 eq1 : BodyEqual declarations face x y} -> {0 eq2 : BodyEqual declarations face y z} -> DimensionEvidence env target eq1 -> DimensionEvidence env target eq2 ->
    DimensionEvidence env target (BodyTrans eq1 eq2)
  DimLeft : {0 context : Vect n LogicalType} -> {0 paths : Vect k LogicalType} -> {0 declarations : PathDeclarations context paths} -> {0 face : ScopedFace d} -> {0 i : ScopedInterval d} -> {0 name : LogicalVar paths a} -> {0 left, right : LogicalTerm context a} -> {0 p : DeclaredPath declarations name left right} ->
    {0 entails : boundedEndpointEntails face i False = True} -> boundedEndpointEntails target (substituteScoped env i) False = True ->
    DimensionEvidence env target (BodyEndpoint (DeclaredLeft {face} {i} p entails))
  DimRight : {0 context : Vect n LogicalType} -> {0 paths : Vect k LogicalType} -> {0 declarations : PathDeclarations context paths} -> {0 face : ScopedFace d} -> {0 i : ScopedInterval d} -> {0 name : LogicalVar paths a} -> {0 left, right : LogicalTerm context a} -> {0 p : DeclaredPath declarations name left right} ->
    {0 entails : boundedEndpointEntails face i True = True} -> boundedEndpointEntails target (substituteScoped env i) True = True ->
    DimensionEvidence env target (BodyEndpoint (DeclaredRight {face} {i} p entails))
  DimRestrict : DimensionEvidence env (substituteScopedFace env source) eq ->
    boundedFaceEntails target (substituteScopedFace env source) = True ->
    DimensionEvidence env target (BodyRestrict {face} {source} eq entails)
  DimApp : {0 f : BodyEqual declarations face f1 f2} -> {0 x : BodyEqual declarations face x1 x2} -> DimensionEvidence env target f -> DimensionEvidence env target x -> DimensionEvidence env target (BodyAppEqual f x)
  DimIf : {0 c : BodyEqual declarations face c1 c2} -> {0 t : BodyEqual declarations face t1 t2} -> {0 f : BodyEqual declarations face f1 f2} -> DimensionEvidence env target c -> DimensionEvidence env target t -> DimensionEvidence env target f ->
    DimensionEvidence env target (BodyIfEqual c t f)
  DimUnitElim : {0 x : BodyEqual declarations face x1 x2} -> {0 b : BodyEqual declarations face b1 b2} -> DimensionEvidence env target x -> DimensionEvidence env target b -> DimensionEvidence env target (BodyUnitElimEqual x b)

||| Limits for the first-order substitution preflight, independent of proof fuel.
public export
record ShadowSubstitutionBounds where
  constructor MkShadowSubstitutionBounds
  maxScope : Nat
  inputNodes : Nat
  outputNodes : Nat

shadowEnvironmentNodes : Nat -> Vect n (ScopedInterval d) -> Maybe Nat
shadowEnvironmentNodes fuel [] = Just fuel
shadowEnvironmentNodes Z (_ :: _) = Nothing
shadowEnvironmentNodes (S fuel) (x :: xs) = do
  rest <- intervalNodes fuel x
  shadowEnvironmentNodes rest xs

shadowMappedIntervalNodes : Nat -> Vect n (ScopedInterval d) -> ScopedInterval n -> Maybe Nat
shadowMappedIntervalNodes Z _ _ = Nothing
shadowMappedIntervalNodes (S fuel) env Zero = Just fuel
shadowMappedIntervalNodes (S fuel) env One = Just fuel
shadowMappedIntervalNodes fuel env (Var i) = intervalNodes fuel (index i env)
shadowMappedIntervalNodes (S fuel) env (Reverse x) = shadowMappedIntervalNodes fuel env x
shadowMappedIntervalNodes (S fuel) env (Meet x y) = do
  rest <- shadowMappedIntervalNodes fuel env x
  shadowMappedIntervalNodes rest env y
shadowMappedIntervalNodes (S fuel) env (Join x y) = do
  rest <- shadowMappedIntervalNodes fuel env x
  shadowMappedIntervalNodes rest env y

-- Reverse does not produce a face node in scopedEndpoint.
shadowEndpointNodes : Nat -> ScopedInterval d -> Maybe Nat
shadowEndpointNodes fuel (Reverse x) = shadowEndpointNodes fuel x
shadowEndpointNodes Z _ = Nothing
shadowEndpointNodes (S fuel) Zero = Just fuel
shadowEndpointNodes (S fuel) One = Just fuel
shadowEndpointNodes (S fuel) (Var _) = Just fuel
shadowEndpointNodes (S fuel) (Meet x y) = do
  rest <- shadowEndpointNodes fuel x
  shadowEndpointNodes rest y
shadowEndpointNodes (S fuel) (Join x y) = do
  rest <- shadowEndpointNodes fuel x
  shadowEndpointNodes rest y

shadowMappedFaceNodes : Nat -> Vect n (ScopedInterval d) -> ScopedFace n -> Maybe Nat
shadowMappedFaceNodes Z _ _ = Nothing
shadowMappedFaceNodes (S fuel) env SBottom = Just fuel
shadowMappedFaceNodes (S fuel) env STop = Just fuel
shadowMappedFaceNodes fuel env (SEndpoint i _) = shadowEndpointNodes fuel (index i env)
shadowMappedFaceNodes (S fuel) env (SConjunction x y) = do
  rest <- shadowMappedFaceNodes fuel env x
  shadowMappedFaceNodes rest env y
shadowMappedFaceNodes (S fuel) env (SDisjunction x y) = do
  rest <- shadowMappedFaceNodes fuel env x
  shadowMappedFaceNodes rest env y

||| Admission only: returns remaining output-node allowance without constructing
||| the substitution. All vector entries, including unused ones, are admitted.
public export
boundedShadowIntervalPreflight : {n, d : Nat} -> ShadowSubstitutionBounds ->
  Vect n (ScopedInterval d) -> ScopedInterval n -> Maybe Nat
boundedShadowIntervalPreflight {n} {d} bounds env source =
  if n <= maxScope bounds && d <= maxScope bounds then do
    rest <- shadowEnvironmentNodes (inputNodes bounds) env
    _ <- intervalNodes rest source
    shadowMappedIntervalNodes (outputNodes bounds) env source
  else Nothing

||| As above, accounting exactly for scopedEndpoint's erased reversals.
public export
boundedShadowFacePreflight : {n, d : Nat} -> ShadowSubstitutionBounds ->
  Vect n (ScopedInterval d) -> ScopedFace n -> Maybe Nat
boundedShadowFacePreflight {n} {d} bounds env source =
  if n <= maxScope bounds && d <= maxScope bounds then do
    rest <- shadowEnvironmentNodes (inputNodes bounds) env
    _ <- faceNodes rest source
    shadowMappedFaceNodes (outputNodes bounds) env source
  else Nothing

-- All three allowances are threaded left to right across the entire proof.
shadowProofPreflight : {0 declarations : PathDeclarations context paths} ->
  {0 face : ScopedFace n} -> {0 x, y : PathBody context paths n a} ->
  Nat -> Nat -> Nat -> Vect n (ScopedInterval d) ->
  BodyEqual declarations face x y -> Maybe (Nat, Nat, Nat)
shadowProofPreflight Z input output env eq = Nothing
shadowProofPreflight (S fuel) input output env BodyRefl = Just (fuel, input, output)
shadowProofPreflight (S fuel) input output env (BodySym eq) =
  shadowProofPreflight fuel input output env eq
shadowProofPreflight (S fuel) input output env (BodyTrans x y) = do
  (f, i, o) <- shadowProofPreflight fuel input output env x
  shadowProofPreflight f i o env y
shadowProofPreflight (S fuel) input output env (BodyEndpoint (DeclaredLeft {i} p entails)) = do
  rest <- intervalNodes input i
  out <- shadowMappedIntervalNodes output env i
  Just (fuel, rest, out)
shadowProofPreflight (S fuel) input output env (BodyEndpoint (DeclaredRight {i} p entails)) = do
  rest <- intervalNodes input i
  out <- shadowMappedIntervalNodes output env i
  Just (fuel, rest, out)
shadowProofPreflight (S fuel) input output env (BodyRestrict {source} eq entails) = do
  rest <- faceNodes input source
  out <- shadowMappedFaceNodes output env source
  out2 <- shadowMappedFaceNodes out env source
  shadowProofPreflight fuel rest out2 env eq
shadowProofPreflight (S fuel) input output env (BodyAppEqual x y) = do
  (f, i, o) <- shadowProofPreflight fuel input output env x
  shadowProofPreflight f i o env y
shadowProofPreflight (S fuel) input output env (BodyIfEqual x y z) = do
  (f, i, o) <- shadowProofPreflight fuel input output env x
  (f2, i2, o2) <- shadowProofPreflight f i o env y
  shadowProofPreflight f2 i2 o2 env z
shadowProofPreflight (S fuel) input output env (BodyUnitElimEqual x y) = do
  (f, i, o) <- shadowProofPreflight fuel input output env x
  shadowProofPreflight f i o env y

||| Checks retained proof fields before constructing any substituted syntax.
||| Input allowance includes the whole environment and target face; output
||| allowance counts every endpoint and twice every restriction substitution.
||| This does not bound solver internals, Fin indexing, unary fuel, erased
||| indices, or the cost of producing or evaluating the supplied inputs.
public export
boundedShadowProofPreflight : {n, d : Nat} ->
  {0 declarations : PathDeclarations context paths} -> {0 face : ScopedFace n} ->
  {0 x, y : PathBody context paths n a} ->
  ShadowSubstitutionBounds -> Nat -> Vect n (ScopedInterval d) ->
  ScopedFace d -> BodyEqual declarations face x y -> Maybe (Nat, Nat, Nat)
boundedShadowProofPreflight {n} {d} bounds fuel env target eq =
  if n <= maxScope bounds && d <= maxScope bounds then do
    rest <- shadowEnvironmentNodes (inputNodes bounds) env
    rest2 <- faceNodes rest target
    shadowProofPreflight fuel rest2 (outputNodes bounds) env eq
  else Nothing

||| Trusted-host recertification: fuel counts proof nodes, shared left to right.
||| Substitution functions and their results are not resource bounded.
public export
recertifyDimensionEvidence : {e : Nat} -> {0 declarations : PathDeclarations context paths} ->
  {0 face : ScopedFace d} -> {0 x, y : PathBody context paths d a} ->
  (fuel : Nat) -> (env : Fin d -> ScopedInterval e) -> (target : ScopedFace e) ->
  (eq : BodyEqual declarations face x y) -> (Nat, Maybe (DimensionEvidence env target eq))
recertifyDimensionEvidence Z env target eq = (Z, Nothing)
recertifyDimensionEvidence (S fuel) env target BodyRefl = (fuel, Just DimRefl)
recertifyDimensionEvidence (S fuel) env target (BodySym eq) =
  let (remaining, result) = recertifyDimensionEvidence fuel env target eq in
  (remaining, map DimSym result)
recertifyDimensionEvidence (S fuel) env target (BodyTrans x y) =
  case recertifyDimensionEvidence fuel env target x of
    (remaining, Nothing) => (remaining, Nothing)
    (remaining, Just cx) =>
      case recertifyDimensionEvidence remaining env target y of
        (rest, Nothing) => (rest, Nothing)
        (rest, Just cy) => (rest, Just (DimTrans cx cy))
recertifyDimensionEvidence (S fuel) env target (BodyEndpoint (DeclaredLeft {i} p entails)) =
  case decEq (boundedEndpointEntails target (substituteScoped env i) False) True of
    Yes check => (fuel, Just (DimLeft check))
    No _ => (fuel, Nothing)
recertifyDimensionEvidence (S fuel) env target (BodyEndpoint (DeclaredRight {i} p entails)) =
  case decEq (boundedEndpointEntails target (substituteScoped env i) True) True of
    Yes check => (fuel, Just (DimRight check))
    No _ => (fuel, Nothing)
recertifyDimensionEvidence (S fuel) env target (BodyRestrict {source} eq entails) =
  case decEq (boundedFaceEntails target (substituteScopedFace env source)) True of
    No _ => (fuel, Nothing)
    Yes check => case recertifyDimensionEvidence fuel env (substituteScopedFace env source) eq of
      (rest, Nothing) => (rest, Nothing)
      (rest, Just cert) => (rest, Just (DimRestrict cert check))
recertifyDimensionEvidence (S fuel) env target (BodyAppEqual f x) =
  case recertifyDimensionEvidence fuel env target f of
    (remaining, Nothing) => (remaining, Nothing)
    (remaining, Just cf) => case recertifyDimensionEvidence remaining env target x of
      (rest, Nothing) => (rest, Nothing)
      (rest, Just cx) => (rest, Just (DimApp cf cx))
recertifyDimensionEvidence (S fuel) env target (BodyIfEqual c t f) =
  case recertifyDimensionEvidence fuel env target c of
    (remaining, Nothing) => (remaining, Nothing)
    (remaining, Just cc) => case recertifyDimensionEvidence remaining env target t of
      (remaining2, Nothing) => (remaining2, Nothing)
      (remaining2, Just ct) => case recertifyDimensionEvidence remaining2 env target f of
        (rest, Nothing) => (rest, Nothing)
        (rest, Just cf) => (rest, Just (DimIf cc ct cf))
recertifyDimensionEvidence (S fuel) env target (BodyUnitElimEqual x b) =
  case recertifyDimensionEvidence fuel env target x of
    (remaining, Nothing) => (remaining, Nothing)
    (remaining, Just cx) => case recertifyDimensionEvidence remaining env target b of
      (rest, Nothing) => (rest, Nothing)
      (rest, Just cb) => (rest, Just (DimUnitElim cx cb))

||| Finite admission precedes the existing recertifier. Success carries
||| evidence for precisely the supplied proof and target, not a time bound.
public export
recertifyFiniteDimensionEvidence : {n, d : Nat} ->
  {0 declarations : PathDeclarations context paths} -> {0 face : ScopedFace n} ->
  {0 x, y : PathBody context paths n a} ->
  (bounds : ShadowSubstitutionBounds) -> (fuel : Nat) ->
  (env : Vect n (ScopedInterval d)) -> (target : ScopedFace d) ->
  (eq : BodyEqual declarations face x y) ->
  Maybe (DimensionEvidence (\i => index i env) target eq)
recertifyFiniteDimensionEvidence bounds fuel env target eq =
  case boundedShadowProofPreflight bounds fuel env target eq of
    Nothing => Nothing
    Just _ => snd (recertifyDimensionEvidence fuel (\i => index i env) target eq)

public export
mapBodyEqualDimensions : {0 declarations : PathDeclarations context paths} ->
  {0 face : ScopedFace d} -> {0 x, y : PathBody context paths d a} ->
  (env : Fin d -> ScopedInterval e) -> (0 target : ScopedFace e) -> (eq : BodyEqual declarations face x y) ->
  DimensionEvidence env target eq ->
  BodyEqual declarations target
    (mapPathDimensions env x) (mapPathDimensions env y)
mapBodyEqualDimensions env target BodyRefl DimRefl = BodyRefl
mapBodyEqualDimensions env target (BodySym eq) (DimSym cert) = BodySym (mapBodyEqualDimensions env target eq cert)
mapBodyEqualDimensions env target (BodyTrans x y) (DimTrans cx cy) = BodyTrans (mapBodyEqualDimensions env target x cx) (mapBodyEqualDimensions env target y cy)
mapBodyEqualDimensions env target (BodyEndpoint (DeclaredLeft p entails)) (DimLeft check) = BodyEndpoint (DeclaredLeft p check)
mapBodyEqualDimensions env target (BodyEndpoint (DeclaredRight p entails)) (DimRight check) = BodyEndpoint (DeclaredRight p check)
mapBodyEqualDimensions env target (BodyRestrict eq entails) (DimRestrict cert check) = BodyRestrict (mapBodyEqualDimensions env _ eq cert) check
mapBodyEqualDimensions env target (BodyAppEqual f x) (DimApp cf cx) = BodyAppEqual (mapBodyEqualDimensions env target f cf) (mapBodyEqualDimensions env target x cx)
mapBodyEqualDimensions env target (BodyIfEqual c t f) (DimIf cc ct cf) = BodyIfEqual (mapBodyEqualDimensions env target c cc) (mapBodyEqualDimensions env target t ct) (mapBodyEqualDimensions env target f cf)
mapBodyEqualDimensions env target (BodyUnitElimEqual x b) (DimUnitElim cx cb) = BodyUnitElimEqual (mapBodyEqualDimensions env target x cx) (mapBodyEqualDimensions env target b cb)

||| Both boundaries are checked in the extended dimension scope, under the
||| weakened ambient restriction conjoined with the corresponding binder face.
public export
data DeclaredShadowPath : (declarations : PathDeclarations context paths) ->
  (face : ScopedFace d) -> PathBody context paths d a -> PathBody context paths d a -> Type where
  ShadowAbstract : (body : PathBody context paths (S d) a) ->
    BodyEqual declarations (SConjunction (weakenFace face) (SEndpoint FZ False))
      body (mapPathDimensions (Var . FS) left) ->
    BodyEqual declarations (SConjunction (weakenFace face) (SEndpoint FZ True))
      body (mapPathDimensions (Var . FS) right) ->
    DeclaredShadowPath declarations face left right

public export
applyDeclaredShadowPath : {0 context : Vect n LogicalType} -> {0 paths : Vect k LogicalType} ->
  {0 d : Nat} -> {0 a : LogicalType} -> {0 declarations : PathDeclarations context paths} ->
  {0 face : ScopedFace d} -> {0 left, right : PathBody context paths d a} ->
  DeclaredShadowPath declarations face left right -> ScopedInterval d -> PathBody context paths d a
applyDeclaredShadowPath (ShadowAbstract body _ _) i = mapPathDimensions (atDimension i) body

||| Generic boundary transport for any checked abstraction, with explicit
||| recertification of the checks actually used at the ambient face.
public export
declaredShadowAtZero : {0 declarations : PathDeclarations context paths} ->
  {0 face : ScopedFace d} -> {0 left, right : PathBody context paths d a} ->
  (body : PathBody context paths (S d) a) ->
  (zero : BodyEqual declarations (SConjunction (weakenFace face) (SEndpoint FZ False)) body (mapPathDimensions (Var . FS) left)) ->
  (one : BodyEqual declarations (SConjunction (weakenFace face) (SEndpoint FZ True)) body (mapPathDimensions (Var . FS) right)) ->
  DimensionEvidence (atDimension Zero) face zero ->
  BodyEqual declarations face (applyDeclaredShadowPath (the (DeclaredShadowPath declarations face left right) (ShadowAbstract body zero one)) Zero) left
declaredShadowAtZero {left} body zero one cert =
  rewrite sym (pathDimensionsRestored Zero left) in mapBodyEqualDimensions (atDimension Zero) _ zero cert

public export
declaredShadowAtOne : {0 declarations : PathDeclarations context paths} ->
  {0 face : ScopedFace d} -> {0 left, right : PathBody context paths d a} ->
  (body : PathBody context paths (S d) a) ->
  (zero : BodyEqual declarations (SConjunction (weakenFace face) (SEndpoint FZ False)) body (mapPathDimensions (Var . FS) left)) ->
  (one : BodyEqual declarations (SConjunction (weakenFace face) (SEndpoint FZ True)) body (mapPathDimensions (Var . FS) right)) ->
  DimensionEvidence (atDimension One) face one ->
  BodyEqual declarations face (applyDeclaredShadowPath (the (DeclaredShadowPath declarations face left right) (ShadowAbstract body zero one)) One) right
declaredShadowAtOne {right} body zero one cert =
  rewrite sym (pathDimensionsRestored One right) in mapBodyEqualDimensions (atDimension One) _ one cert

||| Certificate for the actual path and its chosen ambient face.
public export
ZeroApplicationEvidence : (face : ScopedFace d) -> (left, right : PathBody context paths d a) ->
  DeclaredShadowPath declarations face left right -> Type
ZeroApplicationEvidence face left right (ShadowAbstract body zero one) =
  DimensionEvidence (atDimension Zero) face zero

public export
shadowApplicationZero : (face : ScopedFace d) -> (left, right : PathBody context paths d a) ->
  (path : DeclaredShadowPath declarations face left right) -> ZeroApplicationEvidence face left right path ->
  BodyEqual declarations face (applyDeclaredShadowPath path Zero) left
shadowApplicationZero face left right (ShadowAbstract body zero one) cert =
  declaredShadowAtZero body zero one cert

public export
OneApplicationEvidence : (face : ScopedFace d) -> (left, right : PathBody context paths d a) ->
  DeclaredShadowPath declarations face left right -> Type
OneApplicationEvidence face left right (ShadowAbstract body zero one) =
  DimensionEvidence (atDimension One) face one

public export
shadowApplicationOne : (face : ScopedFace d) -> (left, right : PathBody context paths d a) ->
  (path : DeclaredShadowPath declarations face left right) -> OneApplicationEvidence face left right path ->
  BodyEqual declarations face (applyDeclaredShadowPath path One) right
shadowApplicationOne face left right (ShadowAbstract body zero one) cert =
  declaredShadowAtOne body zero one cert

-- Tabulation agrees pointwise; function extensionality is not assumed.
shadowIndexTabulate : (f : Fin n -> a) -> (i : Fin n) -> index i (tabulate f) = f i
shadowIndexTabulate f FZ = Refl
shadowIndexTabulate f (FS i) = shadowIndexTabulate (f . FS) i

shadowEndpointVector : {d : Nat} -> ScopedInterval d -> Vect (S d) (ScopedInterval d)
shadowEndpointVector side = side :: tabulate Var

shadowEndpointIndex : (side : ScopedInterval d) -> (i : Fin (S d)) ->
  index i (side :: tabulate Var) = atDimension side i
shadowEndpointIndex side FZ = Refl
shadowEndpointIndex side (FS i) = shadowIndexTabulate Var i

shadowPathDimensionsCongruence : (env, env' : Fin d -> ScopedInterval e) ->
  ((i : Fin d) -> env i = env' i) -> (body : PathBody context paths d a) ->
  mapPathDimensions env body = mapPathDimensions env' body
shadowPathDimensionsCongruence env env' h (Embed t) = Refl
shadowPathDimensionsCongruence env env' h (NeutralAt p i) =
  cong (NeutralAt p) (intervalSubstitutionCongruence env env' h i)
shadowPathDimensionsCongruence env env' h (BodyLam b) = cong BodyLam (shadowPathDimensionsCongruence env env' h b)
shadowPathDimensionsCongruence env env' h (BodyApp f x) = cong2 BodyApp (shadowPathDimensionsCongruence env env' h f) (shadowPathDimensionsCongruence env env' h x)
shadowPathDimensionsCongruence env env' h (BodyUnitElim x b) = cong2 BodyUnitElim (shadowPathDimensionsCongruence env env' h x) (shadowPathDimensionsCongruence env env' h b)
shadowPathDimensionsCongruence env env' h (BodyIf c t f) = rewrite shadowPathDimensionsCongruence env env' h c in rewrite shadowPathDimensionsCongruence env env' h t in rewrite shadowPathDimensionsCongruence env env' h f in Refl

||| Finite admission bounds retained proof inputs, not whole-body mapping or runtime.
public export
shadowApplicationZeroFinite : {d : Nat} -> (bounds : ShadowSubstitutionBounds) -> (fuel : Nat) ->
  (face : ScopedFace d) -> (left, right : PathBody context paths d a) ->
  (path : DeclaredShadowPath declarations face left right) ->
  Maybe (BodyEqual declarations face (applyDeclaredShadowPath path Zero) left)
shadowApplicationZeroFinite {d} bounds fuel face left right (ShadowAbstract body zero one) =
  if S d <= maxScope bounds then
    case recertifyFiniteDimensionEvidence bounds fuel (shadowEndpointVector {d} Zero) face zero of
      Nothing => Nothing
      Just cert =>
        let eq = mapBodyEqualDimensions (\i => index i (shadowEndpointVector {d} Zero)) face zero cert in
        Just (rewrite sym (pathDimensionsRestored Zero left) in
              rewrite sym (shadowPathDimensionsCongruence (\i => index i (shadowEndpointVector {d} Zero)) (atDimension Zero) (shadowEndpointIndex Zero) body) in
              rewrite sym (shadowPathDimensionsCongruence (\i => index i (shadowEndpointVector {d} Zero)) (atDimension Zero) (shadowEndpointIndex Zero) (mapPathDimensions (Var . FS) left)) in eq)
  else Nothing

||| As above, for the one boundary.
public export
shadowApplicationOneFinite : {d : Nat} -> (bounds : ShadowSubstitutionBounds) -> (fuel : Nat) ->
  (face : ScopedFace d) -> (left, right : PathBody context paths d a) ->
  (path : DeclaredShadowPath declarations face left right) ->
  Maybe (BodyEqual declarations face (applyDeclaredShadowPath path One) right)
shadowApplicationOneFinite {d} bounds fuel face left right (ShadowAbstract body zero one) =
  if S d <= maxScope bounds then
    case recertifyFiniteDimensionEvidence bounds fuel (shadowEndpointVector {d} One) face one of
      Nothing => Nothing
      Just cert =>
        let eq = mapBodyEqualDimensions (\i => index i (shadowEndpointVector {d} One)) face one cert in
        Just (rewrite sym (pathDimensionsRestored One right) in
              rewrite sym (shadowPathDimensionsCongruence (\i => index i (shadowEndpointVector {d} One)) (atDimension One) (shadowEndpointIndex One) body) in
              rewrite sym (shadowPathDimensionsCongruence (\i => index i (shadowEndpointVector {d} One)) (atDimension One) (shadowEndpointIndex One) (mapPathDimensions (Var . FS) right)) in eq)
  else Nothing

||| Attempt the zero boundary for a trusted host input and proof-node budget.
public export
shadowApplicationZeroAuto : {d : Nat} -> (fuel : Nat) -> (face : ScopedFace d) ->
  (left, right : PathBody context paths d a) ->
  (path : DeclaredShadowPath declarations face left right) ->
  Maybe (BodyEqual declarations face (applyDeclaredShadowPath path Zero) left)
shadowApplicationZeroAuto fuel face left right (ShadowAbstract body zero one) =
  case recertifyDimensionEvidence fuel (atDimension Zero) face zero of
    (_, Nothing) => Nothing
    (_, Just cert) => Just (declaredShadowAtZero body zero one cert)

||| Attempt the one boundary for a trusted host input and proof-node budget.
public export
shadowApplicationOneAuto : {d : Nat} -> (fuel : Nat) -> (face : ScopedFace d) ->
  (left, right : PathBody context paths d a) ->
  (path : DeclaredShadowPath declarations face left right) ->
  Maybe (BodyEqual declarations face (applyDeclaredShadowPath path One) right)
shadowApplicationOneAuto fuel face left right (ShadowAbstract body zero one) =
  case recertifyDimensionEvidence fuel (atDimension One) face one of
    (_, Nothing) => Nothing
    (_, Just cert) => Just (declaredShadowAtOne body zero one cert)

public export
substituteDeclaredShadowPath : {0 context : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  {0 paths : Vect k LogicalType} -> {0 d : Nat} -> {0 a : LogicalType} ->
  {0 declarations : PathDeclarations context paths} -> {0 face : ScopedFace d} ->
  {0 left, right : PathBody context paths d a} -> (sigma : LogicalSubstitution context target) ->
  DeclaredShadowPath declarations face left right ->
  DeclaredShadowPath (substitutePathDeclarations sigma declarations) face
    (mapPathTerms sigma left) (mapPathTerms sigma right)
substituteDeclaredShadowPath {left} {right} sigma (ShadowAbstract body zero one) =
  ShadowAbstract (mapPathTerms sigma body)
    (rewrite pathMixedSubstitution sigma (Var . FS) left in substituteBodyEqual sigma zero)
    (rewrite pathMixedSubstitution sigma (Var . FS) right in substituteBodyEqual sigma one)

||| Dimension substitution is admitted for a declared endpoint only after
||| rechecking the substituted restriction and interval. The bounded solver's
||| acceptance is not assumed to be stable under substitution.
public export
mapDeclaredLeftDimensions : {0 declarations : PathDeclarations context paths} ->
  {0 face : ScopedFace d} -> {0 p : LogicalVar paths a} ->
  {0 left, right : LogicalTerm context a} -> {i : ScopedInterval d} ->
  (env : Fin d -> ScopedInterval e) -> DeclaredPath declarations p left right ->
  boundedEndpointEntails (substituteScopedFace env face) (substituteScoped env i) False = True ->
  DeclaredEndpoint declarations (substituteScopedFace env face)
    (mapPathDimensions env (NeutralAt p i)) (mapPathDimensions env (Embed left))
mapDeclaredLeftDimensions env declared entails = DeclaredLeft declared entails

public export
mapDeclaredRightDimensions : {0 declarations : PathDeclarations context paths} ->
  {0 face : ScopedFace d} -> {0 p : LogicalVar paths a} ->
  {0 left, right : LogicalTerm context a} -> {i : ScopedInterval d} ->
  (env : Fin d -> ScopedInterval e) -> DeclaredPath declarations p left right ->
  boundedEndpointEntails (substituteScopedFace env face) (substituteScoped env i) True = True ->
  DeclaredEndpoint declarations (substituteScopedFace env face)
    (mapPathDimensions env (NeutralAt p i)) (mapPathDimensions env (Embed right))
mapDeclaredRightDimensions env declared entails = DeclaredRight declared entails

public export
substituteDeclaredShadowApplication : {0 context : Vect n LogicalType} -> {0 target : Vect m LogicalType} ->
  {0 paths : Vect k LogicalType} -> {0 d : Nat} -> {0 a : LogicalType} ->
  {0 declarations : PathDeclarations context paths} -> {0 face : ScopedFace d} ->
  {0 left, right : PathBody context paths d a} -> (sigma : LogicalSubstitution context target) ->
  (path : DeclaredShadowPath declarations face left right) -> (i : ScopedInterval d) ->
  applyDeclaredShadowPath (substituteDeclaredShadowPath sigma path) i =
    mapPathTerms sigma (applyDeclaredShadowPath path i)
substituteDeclaredShadowApplication sigma (ShadowAbstract body zero one) i =
  pathMixedSubstitution sigma (atDimension i) body
