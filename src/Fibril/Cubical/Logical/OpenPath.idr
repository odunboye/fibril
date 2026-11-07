-- A deliberately small, independent open logical path experiment.
module Fibril.Cubical.Logical.OpenPath

import Data.Fin
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Restriction

%default total

||| In a context of m abstract A-variables, there is one neutral path p : Path A left right.
public export
record NeutralPath (m : Nat) where
  constructor PathBetween
  left : Fin m
  right : Fin m

||| The only A-terms in this slice: variables and application of that neutral path.
public export
data OpenTerm : Nat -> Nat -> Type where
  AVar : Fin m -> OpenTerm m n
  At : ScopedInterval n -> OpenTerm m n

||| Reindex dimensions without touching term variables.
public export
mapDimensions : (Fin n -> ScopedInterval k) -> OpenTerm m n -> OpenTerm m k
mapDimensions env (AVar x) = AVar x
mapDimensions env (At r) = At (substituteScoped env r)

||| Rename A-variables; the neutral path declaration must be renamed separately.
public export
renameTerms : (Fin m -> Fin k) -> OpenTerm m n -> OpenTerm k n
renameTerms env (AVar x) = AVar (env x)
renameTerms env (At r) = At r

public export
renamePath : (Fin m -> Fin k) -> NeutralPath m -> NeutralPath k
renamePath env (PathBetween l r) = PathBetween (env l) (env r)

public export
data Result = Accepted | Rejected | Exhausted

-- Thread an admission allowance, and impose a fixed cap before calling the
-- potentially exponential face solver. This bounds solver input independently
-- of the caller's allowance; it is not a precise solver-operation budget.
intervalNodes : Nat -> ScopedInterval n -> Maybe Nat
intervalNodes Z _ = Nothing
intervalNodes (S fuel) Zero = Just fuel
intervalNodes (S fuel) One = Just fuel
intervalNodes (S fuel) (Var _) = Just fuel
intervalNodes (S fuel) (Reverse x) = intervalNodes fuel x
intervalNodes (S fuel) (Meet x y) = intervalNodes fuel x >>= \rest => intervalNodes rest y
intervalNodes (S fuel) (Join x y) = intervalNodes fuel x >>= \rest => intervalNodes rest y

faceNodes : Nat -> ScopedFace n -> Maybe Nat
faceNodes Z _ = Nothing
faceNodes (S fuel) SBottom = Just fuel
faceNodes (S fuel) STop = Just fuel
faceNodes (S fuel) (SEndpoint _ _) = Just fuel
faceNodes (S fuel) (SConjunction x y) = faceNodes fuel x >>= \rest => faceNodes rest y
faceNodes (S fuel) (SDisjunction x y) = faceNodes fuel x >>= \rest => faceNodes rest y

||| Restricted conversion of an A-term to an A-variable. Only endpoint
||| computation and reflexivity are supported; failure is not inequality.
public export
convertToVariable : Nat -> Restriction n -> NeutralPath m -> OpenTerm m n -> Fin m -> Result
convertToVariable budget (Under face) path term target =
  case faceNodes (min 12 budget) face of
    Nothing => Exhausted
    Just remaining => case term of
      AVar x => if remaining == 0 then Exhausted else
        if x == target || holds (Under face) SBottom then Accepted else Rejected
      At r => case intervalNodes remaining r of
        Nothing => Exhausted
        Just _ =>
          let leftFace = if left path == target then scopedEndpoint r False else SBottom
              rightFace = if right path == target then scopedEndpoint r True else SBottom
           in if holds (Under face) (SDisjunction leftFace rightFace)
                 then Accepted else Rejected

||| Check <i> body against Path A left right by checking both faces.
||| Each face check has the same bounded admission allowance, not a shared one.
public export
checkAbstraction : Nat -> NeutralPath m -> OpenTerm m (S n) -> Fin m -> Fin m -> Result
checkAbstraction budget path body l r =
  case withinBody body of
    Nothing => Exhausted
    Just _ => case convertToVariable budget unrestricted path (mapDimensions replaceZero body) l of
      Accepted => convertToVariable budget unrestricted path (mapDimensions replaceOne body) r
      other => other
  where
    withinBody : OpenTerm m (S n) -> Maybe Nat
    withinBody (AVar _) = case min 12 budget of
      Z => Nothing
      S remaining => Just remaining
    withinBody (At r) = intervalNodes (min 12 budget) r

    replaceZero : Fin (S n) -> ScopedInterval n
    replaceZero FZ = Zero
    replaceZero (FS i) = Var i
    replaceOne : Fin (S n) -> ScopedInterval n
    replaceOne FZ = One
    replaceOne (FS i) = Var i
