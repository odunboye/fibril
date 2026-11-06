-- Experimental raw syntax only: this module does not check path types.
module Fibril.Foundation.DeMorgan.PathSyntax

import Data.Fin
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

||| A dimension-scoped toy syntax, independent of Fibril's trusted checker.
||| Boolean literals are placeholders, not an embedding of core terms.
public export
data PathExpr : Nat -> Type where
  Literal : Bool -> PathExpr n
  Abstract : PathExpr (S n) -> PathExpr n
  Apply : PathExpr n -> ScopedInterval n -> PathExpr n

||| Lift a dimension substitution through a fresh dimension binder.
public export
liftDimensions : (Fin n -> ScopedInterval m) -> Fin (S n) -> ScopedInterval (S m)
liftDimensions env FZ = Var FZ
liftDimensions env (FS i) = weakenInterval (env i)

||| Capture-avoiding simultaneous dimension substitution.
public export
substituteDimensions : (Fin n -> ScopedInterval m) -> PathExpr n -> PathExpr m
substituteDimensions env (Literal b) = Literal b
substituteDimensions env (Abstract body) = Abstract (substituteDimensions (liftDimensions env) body)
substituteDimensions env (Apply p r) = Apply (substituteDimensions env p) (substituteScoped env r)

||| Substitute for the newest dimension.
public export
instantiateDimension : ScopedInterval n -> PathExpr (S n) -> PathExpr n
instantiateDimension value = substituteDimensions replace
  where
    replace : Fin (S n) -> ScopedInterval n
    replace FZ = value
    replace (FS i) = Var i
