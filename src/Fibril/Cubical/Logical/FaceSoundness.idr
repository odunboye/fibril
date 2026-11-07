module Fibril.Cubical.Logical.FaceSoundness

import Data.Fin
import Data.So
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.OpenPath
import Data.Maybe

import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Interval


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

||| Four-element De Morgan lattice, with two incomparable signed generators.
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

||| The distributive four-element lattice; reversal swaps the signed generators.
public export
fourMeet : Four -> Four -> Four
fourMeet DZero _ = DZero
fourMeet DOne y = y
fourMeet DPositive DZero = DZero
fourMeet DPositive DOne = DPositive
fourMeet DPositive DPositive = DPositive
fourMeet DPositive DNegative = DZero
fourMeet DNegative DZero = DZero
fourMeet DNegative DOne = DNegative
fourMeet DNegative DPositive = DZero
fourMeet DNegative DNegative = DNegative

public export
fourReverse : Four -> Four
fourReverse DZero = DOne
fourReverse DOne = DZero
fourReverse DPositive = DNegative
fourReverse DNegative = DPositive

public export
fourJoin : Four -> Four -> Four
fourJoin x y = fourReverse (fourMeet (fourReverse x) (fourReverse y))

public export
evalInterval : (Fin n -> Four) -> ScopedInterval n -> Four
evalInterval env Zero = DZero
evalInterval env One = DOne
evalInterval env (Var i) = env i
evalInterval env (Reverse x) = fourReverse (evalInterval env x)
evalInterval env (Meet x y) = fourMeet (evalInterval env x) (evalInterval env y)
evalInterval env (Join x y) = fourJoin (evalInterval env x) (evalInterval env y)

reverseEndpoint : (x : Four) -> (b : Bool) ->
  fourEndpoint x (not b) = True -> fourEndpoint (fourReverse x) b = True
reverseEndpoint DZero False Refl impossible
reverseEndpoint DZero True p = Refl
reverseEndpoint DOne False p = Refl
reverseEndpoint DOne True Refl impossible
reverseEndpoint DPositive False Refl impossible
reverseEndpoint DPositive True Refl impossible
reverseEndpoint DNegative False Refl impossible
reverseEndpoint DNegative True Refl impossible

meetFalseEndpoint : (x, y : Four) ->
  (fourEndpoint x False || fourEndpoint y False) = True ->
  fourEndpoint (fourMeet x y) False = True
meetFalseEndpoint DZero DZero p = Refl
meetFalseEndpoint DZero DOne p = Refl
meetFalseEndpoint DZero DPositive p = Refl
meetFalseEndpoint DZero DNegative p = Refl
meetFalseEndpoint DOne DZero p = Refl
meetFalseEndpoint DOne DOne Refl impossible
meetFalseEndpoint DOne DPositive Refl impossible
meetFalseEndpoint DOne DNegative Refl impossible
meetFalseEndpoint DPositive DZero p = Refl
meetFalseEndpoint DPositive DOne Refl impossible
meetFalseEndpoint DPositive DPositive Refl impossible
meetFalseEndpoint DPositive DNegative Refl impossible
meetFalseEndpoint DNegative DZero p = Refl
meetFalseEndpoint DNegative DOne Refl impossible
meetFalseEndpoint DNegative DPositive Refl impossible
meetFalseEndpoint DNegative DNegative Refl impossible

meetTrueEndpoint : (x, y : Four) ->
  (fourEndpoint x True && fourEndpoint y True) = True ->
  fourEndpoint (fourMeet x y) True = True
meetTrueEndpoint DZero DZero Refl impossible
meetTrueEndpoint DZero DOne Refl impossible
meetTrueEndpoint DZero DPositive Refl impossible
meetTrueEndpoint DZero DNegative Refl impossible
meetTrueEndpoint DOne DZero Refl impossible
meetTrueEndpoint DOne DOne p = Refl
meetTrueEndpoint DOne DPositive Refl impossible
meetTrueEndpoint DOne DNegative Refl impossible
meetTrueEndpoint DPositive DZero Refl impossible
meetTrueEndpoint DPositive DOne Refl impossible
meetTrueEndpoint DPositive DPositive Refl impossible
meetTrueEndpoint DPositive DNegative Refl impossible
meetTrueEndpoint DNegative DZero Refl impossible
meetTrueEndpoint DNegative DOne Refl impossible
meetTrueEndpoint DNegative DPositive Refl impossible
meetTrueEndpoint DNegative DNegative Refl impossible

joinFalseEndpoint : (x, y : Four) ->
  (fourEndpoint x False && fourEndpoint y False) = True ->
  fourEndpoint (fourJoin x y) False = True
joinFalseEndpoint DZero DZero p = Refl
joinFalseEndpoint DZero DOne Refl impossible
joinFalseEndpoint DZero DPositive Refl impossible
joinFalseEndpoint DZero DNegative Refl impossible
joinFalseEndpoint DOne DZero Refl impossible
joinFalseEndpoint DOne DOne Refl impossible
joinFalseEndpoint DOne DPositive Refl impossible
joinFalseEndpoint DOne DNegative Refl impossible
joinFalseEndpoint DPositive DZero Refl impossible
joinFalseEndpoint DPositive DOne Refl impossible
joinFalseEndpoint DPositive DPositive Refl impossible
joinFalseEndpoint DPositive DNegative Refl impossible
joinFalseEndpoint DNegative DZero Refl impossible
joinFalseEndpoint DNegative DOne Refl impossible
joinFalseEndpoint DNegative DPositive Refl impossible
joinFalseEndpoint DNegative DNegative Refl impossible

joinTrueEndpoint : (x, y : Four) ->
  (fourEndpoint x True || fourEndpoint y True) = True ->
  fourEndpoint (fourJoin x y) True = True
joinTrueEndpoint DZero DZero Refl impossible
joinTrueEndpoint DZero DOne p = Refl
joinTrueEndpoint DZero DPositive Refl impossible
joinTrueEndpoint DZero DNegative Refl impossible
joinTrueEndpoint DOne DZero p = Refl
joinTrueEndpoint DOne DOne p = Refl
joinTrueEndpoint DOne DPositive p = Refl
joinTrueEndpoint DOne DNegative p = Refl
joinTrueEndpoint DPositive DZero Refl impossible
joinTrueEndpoint DPositive DOne p = Refl
joinTrueEndpoint DPositive DPositive Refl impossible
joinTrueEndpoint DPositive DNegative Refl impossible
joinTrueEndpoint DNegative DZero Refl impossible
joinTrueEndpoint DNegative DOne p = Refl
joinTrueEndpoint DNegative DPositive Refl impossible
joinTrueEndpoint DNegative DNegative Refl impossible

||| Extracted endpoint faces are sufficient, but not necessary, for endpoints.
public export
scopedEndpointSound : (env : Fin n -> Four) -> (r : ScopedInterval n) -> (b : Bool) ->
  evalFace (fourValuation env) (scopedEndpoint r b) = True ->
  fourEndpoint (evalInterval env r) b = True
scopedEndpointSound env Zero False p = Refl
scopedEndpointSound env Zero True Refl impossible
scopedEndpointSound env One False Refl impossible
scopedEndpointSound env One True p = Refl
scopedEndpointSound env (Var i) b p = p
scopedEndpointSound env (Reverse x) b p = reverseEndpoint (evalInterval env x) b (scopedEndpointSound env x (not b) p)
scopedEndpointSound env (Meet x y) False p =
  meetFalseEndpoint (evalInterval env x) (evalInterval env y) $
  soToEq $ case soOr (eqToSo p) of
    Left px => orSo (Left (eqToSo (scopedEndpointSound env x False (soToEq px))))
    Right py => orSo (Right (eqToSo (scopedEndpointSound env y False (soToEq py))))
scopedEndpointSound env (Meet x y) True p =
  let (px, py) = soAnd (eqToSo p) in
  meetTrueEndpoint (evalInterval env x) (evalInterval env y) $
    soToEq (andSo (eqToSo (scopedEndpointSound env x True (soToEq px)), eqToSo (scopedEndpointSound env y True (soToEq py))))
scopedEndpointSound env (Join x y) False p =
  let (px, py) = soAnd (eqToSo p) in
  joinFalseEndpoint (evalInterval env x) (evalInterval env y) $
    soToEq (andSo (eqToSo (scopedEndpointSound env x False (soToEq px)), eqToSo (scopedEndpointSound env y False (soToEq py))))
scopedEndpointSound env (Join x y) True p =
  joinTrueEndpoint (evalInterval env x) (evalInterval env y) $
  soToEq $ case soOr (eqToSo p) of
    Left px => orSo (Left (eqToSo (scopedEndpointSound env x True (soToEq px))))
    Right py => orSo (Right (eqToSo (scopedEndpointSound env y True (soToEq py))))

meetRightEndpoint : (x, y : Four) -> fourEndpoint y True = True -> fourMeet x y = x
meetRightEndpoint x DZero Refl impossible
meetRightEndpoint DZero DOne p = Refl
meetRightEndpoint DOne DOne p = Refl
meetRightEndpoint DPositive DOne p = Refl
meetRightEndpoint DNegative DOne p = Refl
meetRightEndpoint x DPositive Refl impossible
meetRightEndpoint x DNegative Refl impossible

meetLeftEndpoint : (x, y : Four) -> fourEndpoint x True = True -> fourMeet x y = y
meetLeftEndpoint DZero y Refl impossible
meetLeftEndpoint DOne y p = Refl
meetLeftEndpoint DPositive y Refl impossible
meetLeftEndpoint DNegative y Refl impossible

||| Restricted interval equivalence is sound in this four-element model.
public export
intervalEquivalentSound : {n : Nat} -> (env : Fin n -> Four) ->
  (face : ScopedFace n) -> (i, j : ScopedInterval n) ->
  IntervalEquivalent face i j -> evalFace (fourValuation env) face = True ->
  evalInterval env i = evalInterval env j
intervalEquivalentSound env face i i IRefl p = Refl
intervalEquivalentSound env face (Meet i j) i (IMeetRightOne entail) p =
  meetRightEndpoint (evalInterval env i) (evalInterval env j)
    (scopedEndpointSound env j True (boundedFaceEntailsSound (fourValuation env) face (scopedEndpoint j True) entail p))
intervalEquivalentSound env face (Meet i j) j (IMeetLeftOne entail) p =
  meetLeftEndpoint (evalInterval env i) (evalInterval env j)
    (scopedEndpointSound env i True (boundedFaceEntailsSound (fourValuation env) face (scopedEndpoint i True) entail p))
