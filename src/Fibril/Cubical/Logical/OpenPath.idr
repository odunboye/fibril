-- A deliberately small, independent open logical path experiment.
module Fibril.Cubical.Logical.OpenPath

import Data.Fin
import Data.List
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
public export
intervalNodes : Nat -> ScopedInterval n -> Maybe Nat
intervalNodes Z _ = Nothing
intervalNodes (S fuel) Zero = Just fuel
intervalNodes (S fuel) One = Just fuel
intervalNodes (S fuel) (Var _) = Just fuel
intervalNodes (S fuel) (Reverse x) = intervalNodes fuel x
intervalNodes (S fuel) (Meet x y) = intervalNodes fuel x >>= \rest => intervalNodes rest y
intervalNodes (S fuel) (Join x y) = intervalNodes fuel x >>= \rest => intervalNodes rest y

public export
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

-- The four-element De Morgan algebra is the product of two Boolean
-- lattices, with reversal swapping and complementing the coordinates.
DM : Type
DM = (Bool, Bool)

intervalNames : ScopedInterval n -> List (Fin n)
intervalNames Zero = []
intervalNames One = []
intervalNames (Var i) = [i]
intervalNames (Reverse x) = intervalNames x
intervalNames (Meet x y) = intervalNames x ++ intervalNames y
intervalNames (Join x y) = intervalNames x ++ intervalNames y

faceNames : ScopedFace n -> List (Fin n)
faceNames SBottom = []
faceNames STop = []
faceNames (SEndpoint i _) = [i]
faceNames (SConjunction x y) = faceNames x ++ faceNames y
faceNames (SDisjunction x y) = faceNames x ++ faceNames y

lookupDM : Fin n -> List (Fin n, DM) -> DM
lookupDM i [] = (False, False)
lookupDM i ((j, value) :: rest) = if i == j then value else lookupDM i rest

evalDM : List (Fin n, DM) -> ScopedInterval n -> DM
evalDM env Zero = (False, False)
evalDM env One = (True, True)
evalDM env (Var i) = lookupDM i env
evalDM env (Reverse x) = let (a, b) = evalDM env x in (not b, not a)
evalDM env (Meet x y) =
  let (a, b) = evalDM env x; (c, d) = evalDM env y in (a && c, b && d)
evalDM env (Join x y) =
  let (a, b) = evalDM env x; (c, d) = evalDM env y in (a || c, b || d)

faceAt : List (Fin n, DM) -> ScopedFace n -> Bool
faceAt env SBottom = False
faceAt env STop = True
faceAt env (SEndpoint i b) = lookupDM i env == (b, b)
faceAt env (SConjunction x y) = faceAt env x && faceAt env y
faceAt env (SDisjunction x y) = faceAt env x || faceAt env y

allAssignments : List (Fin n) -> List (Fin n, DM) -> ScopedFace n ->
                 ScopedInterval n -> ScopedInterval n -> Bool
allAssignments [] env face r s = not (faceAt env face) || evalDM env r == evalDM env s
allAssignments (i :: rest) env face r s =
  all (\v => allAssignments rest ((i, v) :: env) face r s)
      [(False, False), (False, True), (True, False), (True, True)]

||| Compare applications of the single declared neutral path at two dimensions.
||| Rejection is only failure of this sufficient conversion rule. The path
||| argument fixes the shared typed declaration; distinct paths are not expressible.
public export
convertNeutrals : Nat -> Restriction n -> NeutralPath m ->
                  ScopedInterval n -> ScopedInterval n -> Result
convertNeutrals budget (Under face) path r s =
  case faceNodes (min 12 budget) face >>= \fuel =>
       intervalNodes fuel r >>= \fuel => intervalNodes fuel s of
    Nothing => Exhausted
    Just _ => if allAssignments (nub (faceNames face ++ intervalNames r ++ intervalNames s))
                                 [] face r s
                 then Accepted
                 else if left path == right path then
                   case (convertToVariable budget (Under face) path (At r) (left path),
                         convertToVariable budget (Under face) path (At s) (left path)) of
                     (Accepted, Accepted) => Accepted
                     _ => Rejected
                 else Rejected

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
