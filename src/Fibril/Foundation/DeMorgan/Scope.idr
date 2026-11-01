module Fibril.Foundation.DeMorgan.Scope

import Data.Fin
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Face

%default total

||| Dimension indices are de Bruijn indices; 0 is the newest dimension.
public export
ScopedInterval : Nat -> Type
ScopedInterval n = Interval (Fin n)

public export
data ScopedFace : Nat -> Type where
  SBottom : ScopedFace n
  STop : ScopedFace n
  SEndpoint : Fin n -> Bool -> ScopedFace n
  SConjunction : ScopedFace n -> ScopedFace n -> ScopedFace n
  SDisjunction : ScopedFace n -> ScopedFace n -> ScopedFace n

||| Validate every variable, including variables in redundant expressions.
public export
scopeInterval : (n : Nat) -> Interval Nat -> Maybe (ScopedInterval n)
scopeInterval n Zero = Just Zero
scopeInterval n One = Just One
scopeInterval n (Var x) = map Var (natToFin x n)
scopeInterval n (Meet x y) = [| Meet (scopeInterval n x) (scopeInterval n y) |]
scopeInterval n (Join x y) = [| Join (scopeInterval n x) (scopeInterval n y) |]
scopeInterval n (Reverse x) = map Reverse (scopeInterval n x)

public export
scopeFace : (n : Nat) -> Face -> Maybe (ScopedFace n)
scopeFace n Bottom = Just SBottom
scopeFace n Top = Just STop
scopeFace n (Endpoint x b) = map (\i => SEndpoint i b) (natToFin x n)
scopeFace n (Conjunction x y) = [| SConjunction (scopeFace n x) (scopeFace n y) |]
scopeFace n (Disjunction x y) = [| SDisjunction (scopeFace n x) (scopeFace n y) |]

||| Add a newest dimension, shifting all existing references.
public export
weakenInterval : ScopedInterval n -> ScopedInterval (S n)
weakenInterval = substitute (Var . FS)

||| Dimension substitution preserves scope by construction.
public export
substituteScoped : (Fin n -> ScopedInterval m) -> ScopedInterval n -> ScopedInterval m
substituteScoped = substitute

||| Instantiate the newest dimension; older indices shift down.
public export
instantiate : ScopedInterval n -> ScopedInterval (S n) -> ScopedInterval n
instantiate value = substitute replace
  where
    replace : Fin (S n) -> ScopedInterval n
    replace FZ = value
    replace (FS older) = Var older

public export
forgetInterval : ScopedInterval n -> Interval Nat
forgetInterval = substitute (Var . finToNat)

public export
forgetFace : ScopedFace n -> Face
forgetFace SBottom = Bottom
forgetFace STop = Top
forgetFace (SEndpoint i b) = Endpoint (finToNat i) b
forgetFace (SConjunction x y) = Conjunction (forgetFace x) (forgetFace y)
forgetFace (SDisjunction x y) = Disjunction (forgetFace x) (forgetFace y)

||| Extract boundaries without leaving the dimension scope.
public export
scopedEndpoint : ScopedInterval n -> Bool -> ScopedFace n
scopedEndpoint Zero False = STop
scopedEndpoint Zero True = SBottom
scopedEndpoint One False = SBottom
scopedEndpoint One True = STop
scopedEndpoint (Var i) b = SEndpoint i b
scopedEndpoint (Reverse x) b = scopedEndpoint x (not b)
scopedEndpoint (Meet x y) False = SDisjunction (scopedEndpoint x False) (scopedEndpoint y False)
scopedEndpoint (Meet x y) True = SConjunction (scopedEndpoint x True) (scopedEndpoint y True)
scopedEndpoint (Join x y) False = SConjunction (scopedEndpoint x False) (scopedEndpoint y False)
scopedEndpoint (Join x y) True = SDisjunction (scopedEndpoint x True) (scopedEndpoint y True)

public export
substituteScopedFace : (Fin n -> ScopedInterval m) -> ScopedFace n -> ScopedFace m
substituteScopedFace env SBottom = SBottom
substituteScopedFace env STop = STop
substituteScopedFace env (SEndpoint i b) = scopedEndpoint (env i) b
substituteScopedFace env (SConjunction x y) =
  SConjunction (substituteScopedFace env x) (substituteScopedFace env y)
substituteScopedFace env (SDisjunction x y) =
  SDisjunction (substituteScopedFace env x) (substituteScopedFace env y)

public export
weakenFace : ScopedFace n -> ScopedFace (S n)
weakenFace = substituteScopedFace (Var . FS)

public export
instantiateFace : ScopedInterval n -> ScopedFace (S n) -> ScopedFace n
instantiateFace value = substituteScopedFace replace
  where
    replace : Fin (S n) -> ScopedInterval n
    replace FZ = value
    replace (FS older) = Var older

||| Reuse the reference solver only after obtaining a well-scoped face.
public export
entailsScoped : ScopedFace n -> ScopedFace n -> Bool
entailsScoped x y = entails (forgetFace x) (forgetFace y)
