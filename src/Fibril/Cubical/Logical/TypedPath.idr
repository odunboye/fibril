-- A deliberately syntactic declarative judgment, not a runtime checker.
module Fibril.Cubical.Logical.TypedPath

import Data.Fin
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
