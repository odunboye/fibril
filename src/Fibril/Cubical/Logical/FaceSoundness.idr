module Fibril.Cubical.Logical.FaceSoundness

import Data.Fin
import Data.So
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.OpenPath
import Data.Maybe

import Fibril.Foundation.DeMorgan.Scope

%default total

-- Endpoint observations are intentionally independent: this includes ordinary
-- endpoint valuations and non-Boolean observations, without assuming excluded middle.
public export
evalFace : (Fin n -> Bool -> Bool) -> ScopedFace n -> Bool
evalFace env SBottom = False
evalFace env STop = True
evalFace env (SEndpoint i b) = env i b
evalFace env (SConjunction x y) = evalFace env x && evalFace env y
evalFace env (SDisjunction x y) = evalFace env x || evalFace env y

natEq : (x, y : Nat) -> x == y = True -> x = y
natEq Z Z p = Refl
natEq Z (S y) Refl impossible
natEq (S x) Z Refl impossible
natEq (S x) (S y) p = cong S (natEq x y p)

finEq : (x, y : Fin n) -> x == y = True -> x = y
finEq x y p = injective {f = finToNat} (natEq (finToNat x) (finToNat y) p)

boolEq : (x, y : Bool) -> x == y = True -> x = y
boolEq False False p = Refl
boolEq False True Refl impossible
boolEq True False Refl impossible
boolEq True True p = Refl

public export
simpleFaceEntailsSound : (env : Fin n -> Bool -> Bool) -> (phi, psi : ScopedFace n) ->
  simpleFaceEntails phi psi = True -> evalFace env phi = True -> evalFace env psi = True
simpleFaceEntailsSound env SBottom psi p Refl impossible
simpleFaceEntailsSound env STop STop p q = Refl
simpleFaceEntailsSound env (SEndpoint i b) STop p q = Refl
simpleFaceEntailsSound env (SConjunction x y) STop p q = Refl
simpleFaceEntailsSound env (SDisjunction x y) STop p q = Refl
simpleFaceEntailsSound env (SConjunction x y) SBottom p q =
  let (qx, qy) = soAnd (eqToSo q) in
  case soOr (eqToSo p) of
    Left px => simpleFaceEntailsSound env x SBottom (soToEq px) (soToEq qx)
    Right py => simpleFaceEntailsSound env y SBottom (soToEq py) (soToEq qy)
simpleFaceEntailsSound env (SConjunction x y) (SEndpoint i b) p q =
  let (qx, qy) = soAnd (eqToSo q) in
  case soOr (eqToSo p) of
    Left px => simpleFaceEntailsSound env x (SEndpoint i b) (soToEq px) (soToEq qx)
    Right py => simpleFaceEntailsSound env y (SEndpoint i b) (soToEq py) (soToEq qy)
simpleFaceEntailsSound env (SConjunction x y) (SConjunction a b) p q =
  let (qx, qy) = soAnd (eqToSo q) in
  case soOr (eqToSo p) of
    Left px => simpleFaceEntailsSound env x (SConjunction a b) (soToEq px) (soToEq qx)
    Right py => simpleFaceEntailsSound env y (SConjunction a b) (soToEq py) (soToEq qy)
simpleFaceEntailsSound env (SConjunction x y) (SDisjunction a b) p q =
  let (qx, qy) = soAnd (eqToSo q) in
  case soOr (eqToSo p) of
    Left px => simpleFaceEntailsSound env x (SDisjunction a b) (soToEq px) (soToEq qx)
    Right py => simpleFaceEntailsSound env y (SDisjunction a b) (soToEq py) (soToEq qy)
simpleFaceEntailsSound env STop (SDisjunction x y) p q =
  case soOr (eqToSo p) of
    Left px => soToEq (orSo (Left (eqToSo (simpleFaceEntailsSound env STop x (soToEq px) q))))
    Right py => soToEq (orSo (Right (eqToSo (simpleFaceEntailsSound env STop y (soToEq py) q))))
simpleFaceEntailsSound env (SEndpoint i b) (SDisjunction x y) p q =
  case soOr (eqToSo p) of
    Left px => soToEq (orSo (Left (eqToSo (simpleFaceEntailsSound env (SEndpoint i b) x (soToEq px) q))))
    Right py => soToEq (orSo (Right (eqToSo (simpleFaceEntailsSound env (SEndpoint i b) y (soToEq py) q))))
simpleFaceEntailsSound env (SDisjunction a b) (SDisjunction x y) p q =
  case soOr (eqToSo p) of
    Left px => soToEq (orSo (Left (eqToSo (simpleFaceEntailsSound env (SDisjunction a b) x (soToEq px) q))))
    Right py => soToEq (orSo (Right (eqToSo (simpleFaceEntailsSound env (SDisjunction a b) y (soToEq py) q))))
simpleFaceEntailsSound env (SEndpoint i b) (SEndpoint j c) p q =
  let (pi, pb) = soAnd (eqToSo p) in
  case finEq i j (soToEq pi) of
    Refl => case boolEq b c (soToEq pb) of
      Refl => q
simpleFaceEntailsSound env STop SBottom Refl q impossible
simpleFaceEntailsSound env STop (SEndpoint i b) Refl q impossible
simpleFaceEntailsSound env STop (SConjunction x y) Refl q impossible
simpleFaceEntailsSound env (SEndpoint i b) SBottom Refl q impossible
simpleFaceEntailsSound env (SEndpoint i b) (SConjunction x y) Refl q impossible
simpleFaceEntailsSound env (SDisjunction a b) SBottom Refl q impossible
simpleFaceEntailsSound env (SDisjunction a b) (SEndpoint i c) Refl q impossible
simpleFaceEntailsSound env (SDisjunction a b) (SConjunction x y) Refl q impossible

public export
boundedFaceEntailsSound : {n : Nat} -> (env : Fin n -> Bool -> Bool) ->
  (phi, psi : ScopedFace n) -> boundedFaceEntails phi psi = True ->
  evalFace env phi = True -> evalFace env psi = True
boundedFaceEntailsSound {n} env phi psi p q with (n <= 12 && isJust (faceNodes 12 phi >>= \f => faceNodes f psi))
  boundedFaceEntailsSound env phi psi p q | False = absurd p
  boundedFaceEntailsSound env phi psi p q | True = simpleFaceEntailsSound env phi psi p q

||| Four distinguishable interval observations; no operations are defined here.
public export
data Four = DZero | DOne | DPositive | DNegative

||| Whether a four-element interval value is the requested endpoint.
public export
fourEndpoint : Four -> Bool -> Bool
fourEndpoint DZero False = True
fourEndpoint DOne True = True
fourEndpoint _ _ = False

public export
fourValuation : (Fin n -> Four) -> Fin n -> Bool -> Bool
fourValuation env i b = fourEndpoint (env i) b
