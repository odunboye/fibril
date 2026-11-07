module Fibril.Cubical.Logical.ShadowPath

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.Shadow
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
