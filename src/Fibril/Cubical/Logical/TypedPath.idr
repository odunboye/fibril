-- A deliberately syntactic declarative judgment, not a runtime checker.
module Fibril.Cubical.Logical.TypedPath

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

public export
faceZero : Fin (S n) -> ScopedInterval n
faceZero FZ = Zero
faceZero (FS i) = Var i

public export
faceOne : Fin (S n) -> ScopedInterval n
faceOne FZ = One
faceOne (FS i) = Var i

-- The context contains exactly m variables of the abstract base A. Universe
-- denotes A here, not a universe. There are no arbitrary context annotations.
mutual
  public export
  data TypeFormed : Expr m n -> Type where
    Base : TypeFormed Universe
    PathForm : TypeFormed a -> HasType l a -> HasType r a ->
               TypeFormed (Path (weakenDimensions a) l r)

  public export
  data HasType : Expr m n -> Expr m n -> Type where
    BaseVar : (x : Fin m) -> HasType (Variable x) Universe
    PathIntro : TypeFormed a -> HasType l a -> HasType r a ->
                HasType body (weakenDimensions a) ->
                substituteDimensions TypedPath.faceZero body = l ->
                substituteDimensions TypedPath.faceOne body = r ->
                HasType (Abstract body) (Path (weakenDimensions a) l r)
    PathElim : HasType p (Path (weakenDimensions a) l r) ->
               (i : ScopedInterval n) -> HasType (Apply p i) a

-- Separately indexed base and neutral-path declarations: path endpoints can
-- mention only base variables, never the path being declared.
public export
data NeutralExpr : Nat -> Nat -> Nat -> Type where
  NBase : Fin m -> NeutralExpr m k n
  NPath : Fin k -> NeutralExpr m k n
  NType : NeutralExpr m k n
  NPathType : NeutralExpr m k (S n) -> NeutralExpr m k n -> NeutralExpr m k n -> NeutralExpr m k n
  NAbstract : NeutralExpr m k (S n) -> NeutralExpr m k n
  NApply : NeutralExpr m k n -> ScopedInterval n -> NeutralExpr m k n

public export
mapNeutralDimensions : (Fin n -> ScopedInterval d) -> NeutralExpr m k n -> NeutralExpr m k d
mapNeutralDimensions env (NBase x) = NBase x
mapNeutralDimensions env (NPath p) = NPath p
mapNeutralDimensions env NType = NType
mapNeutralDimensions env (NPathType a l r) = NPathType (mapNeutralDimensions (liftDimensions env) a) (mapNeutralDimensions env l) (mapNeutralDimensions env r)
mapNeutralDimensions env (NAbstract body) = NAbstract (mapNeutralDimensions (liftDimensions env) body)
mapNeutralDimensions env (NApply p i) = NApply (mapNeutralDimensions env p) (substituteScoped env i)

public export
weakenNeutralDimensions : NeutralExpr m k n -> NeutralExpr m k (S n)
weakenNeutralDimensions = mapNeutralDimensions (Var . FS)

-- A deliberately incomplete syntactic face entailment: conjunction supplies
-- either assumption, and a disjunction goal needs just one branch.
public export
simpleFaceEntails : ScopedFace n -> ScopedFace n -> Bool
simpleFaceEntails SBottom _ = True
simpleFaceEntails _ STop = True
simpleFaceEntails (SConjunction x y) goal = simpleFaceEntails x goal || simpleFaceEntails y goal
simpleFaceEntails assumption (SDisjunction x y) = simpleFaceEntails assumption x || simpleFaceEntails assumption y
simpleFaceEntails (SEndpoint i x) (SEndpoint j y) = i == j && x == y
simpleFaceEntails _ _ = False

public export
boundedFaceEntails : {n : Nat} -> ScopedFace n -> ScopedFace n -> Bool
boundedFaceEntails {n} assumption goal =
  if n <= 12 && isJust (faceNodes 12 assumption >>= \f => faceNodes f goal)
    then simpleFaceEntails assumption goal else False

mutual
  public export
  data NeutralTypeFormed : PathContext m k -> ScopedFace n -> NeutralExpr m k n -> Type where
    NBaseForm : NeutralTypeFormed ctx face NType
    NPathForm : NeutralTypeFormed ctx face a -> NeutralHasType ctx face l a ->
                NeutralHasType ctx face r a ->
                NeutralTypeFormed ctx face (NPathType (weakenNeutralDimensions a) l r)

  public export
  data NeutralHasType : PathContext m k -> ScopedFace n -> NeutralExpr m k n -> NeutralExpr m k n -> Type where
    NBaseVar : (x : Fin m) -> NeutralHasType ctx face (NBase x) NType
    NPathVar : (p : Fin k) -> NeutralHasType ctx face (NPath p)
      (NPathType NType (NBase (left (index p ctx))) (NBase (right (index p ctx))))
    NIntro : NeutralTypeFormed ctx face a -> NeutralHasType ctx face l a -> NeutralHasType ctx face r a ->
      NeutralHasType ctx (weakenFace face) body (weakenNeutralDimensions a) ->
      NeutralEqual ctx (SConjunction (weakenFace face) (SEndpoint FZ False)) body (weakenNeutralDimensions l) (weakenNeutralDimensions a) ->
      NeutralEqual ctx (SConjunction (weakenFace face) (SEndpoint FZ True)) body (weakenNeutralDimensions r) (weakenNeutralDimensions a) ->
      NeutralHasType ctx face (NAbstract body) (NPathType (weakenNeutralDimensions a) l r)
    NElim : NeutralHasType ctx face p (NPathType (weakenNeutralDimensions a) l r) ->
      (i : ScopedInterval n) -> NeutralHasType ctx face (NApply p i) a

  public export
  data NeutralEqual : PathContext m k -> ScopedFace n -> NeutralExpr m k n -> NeutralExpr m k n -> NeutralExpr m k n -> Type where
    NRefl : NeutralHasType ctx face t a -> NeutralEqual ctx face t t a
    NEndpointLeft : NeutralHasType ctx face p (NPathType (weakenNeutralDimensions a) l r) ->
      NeutralHasType ctx face l a -> boundedFaceEntails face (scopedEndpoint i False) = True ->
      NeutralEqual ctx face (NApply p i) l a
    NEndpointRight : NeutralHasType ctx face p (NPathType (weakenNeutralDimensions a) l r) ->
      NeutralHasType ctx face r a -> boundedFaceEntails face (scopedEndpoint i True) = True ->
      NeutralEqual ctx face (NApply p i) r a
    NAbstractCong : NeutralHasType ctx face (NAbstract x) (NPathType (weakenNeutralDimensions a) l r) ->
      NeutralHasType ctx face (NAbstract y) (NPathType (weakenNeutralDimensions a) l r) ->
      NeutralEqual ctx (weakenFace face) x y (weakenNeutralDimensions a) ->
      NeutralEqual ctx face (NAbstract x) (NAbstract y) (NPathType (weakenNeutralDimensions a) l r)
