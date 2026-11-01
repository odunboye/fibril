-- Raw interval syntax and structural substitution. Vertex evaluation is not
-- a conversion procedure; see docs/foundation-baseline.md.
module Fibril.Foundation.DeMorgan.Interval

%default total

||| De Morgan interval syntax. Variables are supplied by the caller.
||| This is not the face lattice or a conversion decision procedure.
public export
data Interval : Type -> Type where
  Zero : Interval name
  One : Interval name
  Var : name -> Interval name
  Meet : Interval name -> Interval name -> Interval name
  Join : Interval name -> Interval name -> Interval name
  Reverse : Interval name -> Interval name

||| Structural substitution, including replacement by arbitrary expressions.
public export
substitute : (a -> Interval b) -> Interval a -> Interval b
substitute env Zero = Zero
substitute env One = One
substitute env (Var x) = env x
substitute env (Meet x y) = Meet (substitute env x) (substitute env y)
substitute env (Join x y) = Join (substitute env x) (substitute env y)
substitute env (Reverse x) = Reverse (substitute env x)

||| Interpret a vertex assignment only. Agreement at all Boolean vertices does
||| NOT decide equality in the free De Morgan algebra.
public export
atVertex : (name -> Bool) -> Interval name -> Bool
atVertex env Zero = False
atVertex env One = True
atVertex env (Var x) = env x
atVertex env (Meet x y) = atVertex env x && atVertex env y
atVertex env (Join x y) = atVertex env x || atVertex env y
atVertex env (Reverse x) = not (atVertex env x)
