module Fibril.Cubical.Logical.ShadowPath

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.OpenPath

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

||| A declarative endpoint equation, valid only under the displayed face.
||| This is not runtime equality or a quantitative resource theorem.
public export
data DeclaredEndpoint : PathDeclarations context paths -> ScopedFace d ->
  PathBody context paths d a -> PathBody context paths d a -> Type where
  DeclaredLeft : DeclaredPath declarations p left right ->
    boundedEndpointEntails face i False = True ->
    DeclaredEndpoint declarations face (NeutralAt p i) (Embed left)
  DeclaredRight : DeclaredPath declarations p left right ->
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
  BodyRestrict : BodyEqual declarations source x y ->
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
  {0 left, right : LogicalTerm context a} -> {0 i : ScopedInterval d} ->
  (env : Fin d -> ScopedInterval e) -> DeclaredPath declarations p left right ->
  boundedEndpointEntails (substituteScopedFace env face) (substituteScoped env i) False = True ->
  DeclaredEndpoint declarations (substituteScopedFace env face)
    (mapPathDimensions env (NeutralAt p i)) (mapPathDimensions env (Embed left))
mapDeclaredLeftDimensions env declared entails = DeclaredLeft declared entails

public export
mapDeclaredRightDimensions : {0 declarations : PathDeclarations context paths} ->
  {0 face : ScopedFace d} -> {0 p : LogicalVar paths a} ->
  {0 left, right : LogicalTerm context a} -> {0 i : ScopedInterval d} ->
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
