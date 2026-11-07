-- A deliberately small, independent open logical path experiment.
module Fibril.Cubical.Logical.OpenPath

import Data.Fin
import Data.List
import Data.List.Elem

import Data.So
import Language.Reflection
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.NormalForm
import Fibril.Foundation.DeMorgan.Face
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Restriction

%language ElabReflection
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
public export
DM : Type
DM = (Bool, Bool)

public export
intervalNames : ScopedInterval n -> List (Fin n)
intervalNames Zero = []
intervalNames One = []
intervalNames (Var i) = [i]
intervalNames (Reverse x) = intervalNames x
intervalNames (Meet x y) = intervalNames x ++ intervalNames y
intervalNames (Join x y) = intervalNames x ++ intervalNames y

public export
faceNames : ScopedFace n -> List (Fin n)
faceNames SBottom = []
faceNames STop = []
faceNames (SEndpoint i _) = [i]
faceNames (SConjunction x y) = faceNames x ++ faceNames y
faceNames (SDisjunction x y) = faceNames x ++ faceNames y

public export
lookupDM : Fin n -> List (Fin n, DM) -> DM
lookupDM i [] = (False, False)
lookupDM i ((j, value) :: rest) = if i == j then value else lookupDM i rest

public export
dmReverse : DM -> DM
dmReverse x = let (a, b) = x in (not b, not a)

public export
dmMeet : DM -> DM -> DM
dmMeet x y = let (a, b) = x; (c, d) = y in (a && c, b && d)

public export
dmJoin : DM -> DM -> DM
dmJoin x y = let (a, b) = x; (c, d) = y in (a || c, b || d)

public export
evalDM : List (Fin n, DM) -> ScopedInterval n -> DM
evalDM env Zero = (False, False)
evalDM env One = (True, True)
evalDM env (Var i) = lookupDM i env
evalDM env (Reverse x) = dmReverse (evalDM env x)
evalDM env (Meet x y) = dmMeet (evalDM env x) (evalDM env y)
evalDM env (Join x y) = dmJoin (evalDM env x) (evalDM env y)

public export
faceAt : List (Fin n, DM) -> ScopedFace n -> Bool
faceAt env SBottom = False
faceAt env STop = True
faceAt env (SEndpoint i b) = lookupDM i env == (b, b)
faceAt env (SConjunction x y) = faceAt env x && faceAt env y
faceAt env (SDisjunction x y) = faceAt env x || faceAt env y

public export
allAssignments : List (Fin n) -> List (Fin n, DM) -> ScopedFace n ->
                 ScopedInterval n -> ScopedInterval n -> Bool
allAssignments [] env face r s = not (faceAt env face) || evalDM env r == evalDM env s
allAssignments (i :: rest) env face r s =
  all (\v => allAssignments rest ((i, v) :: env) face r s)
      [(False, False), (False, True), (True, False), (True, True)]

public export
intervalEqual : ScopedFace n -> ScopedInterval n -> ScopedInterval n -> Bool
intervalEqual face r s =
  allAssignments (nub (faceNames face ++ intervalNames r ++ intervalNames s)) [] face r s

||| Bounded admission before restricted interval comparison; budget is not work fuel.
public export
restrictedIntervalEqual : {n : Nat} -> Nat -> ScopedFace n -> ScopedInterval n -> ScopedInterval n -> Result
restrictedIntervalEqual {n} budget face r s =
  if not (n <= 12) then Exhausted else
  case faceNodes (min 12 budget) face >>= \f => intervalNodes f r >>= \g => intervalNodes g s of
    Nothing => Exhausted
    Just _ => if intervalEqual face r s then Accepted else Rejected

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
    Just _ => if intervalEqual face r s
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

-- Semantic facts below are stated directly over the solver's list environment,
-- lookup, face evaluator and pair-valued interval evaluator.

dmReverseEndpoint : (x : DM) -> (b : Bool) ->
  (x == (not b, not b)) = True ->
  (dmReverse x == (b, b)) = True
dmReverseEndpoint (False, False) False p = absurd p
dmReverseEndpoint (False, False) True p = Refl
dmReverseEndpoint (False, True) False p = absurd p
dmReverseEndpoint (False, True) True p = absurd p
dmReverseEndpoint (True, False) False p = absurd p
dmReverseEndpoint (True, False) True p = absurd p
dmReverseEndpoint (True, True) False p = Refl
dmReverseEndpoint (True, True) True p = absurd p

dmMeetFalse : (x, y : DM) ->
  ((x == (False, False)) || (y == (False, False))) = True ->
  (dmMeet x y == (False, False)) = True
dmMeetFalse (False, False) (False, False) p = Refl
dmMeetFalse (False, False) (False, True) p = Refl
dmMeetFalse (False, False) (True, False) p = Refl
dmMeetFalse (False, False) (True, True) p = Refl
dmMeetFalse (False, True) (False, False) p = Refl
dmMeetFalse (False, True) (False, True) p = absurd p
dmMeetFalse (False, True) (True, False) p = absurd p
dmMeetFalse (False, True) (True, True) p = absurd p
dmMeetFalse (True, False) (False, False) p = Refl
dmMeetFalse (True, False) (False, True) p = absurd p
dmMeetFalse (True, False) (True, False) p = absurd p
dmMeetFalse (True, False) (True, True) p = absurd p
dmMeetFalse (True, True) (False, False) p = Refl
dmMeetFalse (True, True) (False, True) p = absurd p
dmMeetFalse (True, True) (True, False) p = absurd p
dmMeetFalse (True, True) (True, True) p = absurd p

dmMeetTrue : (x, y : DM) ->
  ((x == (True, True)) && (y == (True, True))) = True ->
  (dmMeet x y == (True, True)) = True
dmMeetTrue (False, False) (False, False) p = absurd p
dmMeetTrue (False, False) (False, True) p = absurd p
dmMeetTrue (False, False) (True, False) p = absurd p
dmMeetTrue (False, False) (True, True) p = absurd p
dmMeetTrue (False, True) (False, False) p = absurd p
dmMeetTrue (False, True) (False, True) p = absurd p
dmMeetTrue (False, True) (True, False) p = absurd p
dmMeetTrue (False, True) (True, True) p = absurd p
dmMeetTrue (True, False) (False, False) p = absurd p
dmMeetTrue (True, False) (False, True) p = absurd p
dmMeetTrue (True, False) (True, False) p = absurd p
dmMeetTrue (True, False) (True, True) p = absurd p
dmMeetTrue (True, True) (False, False) p = absurd p
dmMeetTrue (True, True) (False, True) p = absurd p
dmMeetTrue (True, True) (True, False) p = absurd p
dmMeetTrue (True, True) (True, True) p = Refl

dmJoinFalse : (x, y : DM) ->
  ((x == (False, False)) && (y == (False, False))) = True ->
  (dmJoin x y == (False, False)) = True
dmJoinFalse (False, False) (False, False) p = Refl
dmJoinFalse (False, False) (False, True) p = absurd p
dmJoinFalse (False, False) (True, False) p = absurd p
dmJoinFalse (False, False) (True, True) p = absurd p
dmJoinFalse (False, True) (False, False) p = absurd p
dmJoinFalse (False, True) (False, True) p = absurd p
dmJoinFalse (False, True) (True, False) p = absurd p
dmJoinFalse (False, True) (True, True) p = absurd p
dmJoinFalse (True, False) (False, False) p = absurd p
dmJoinFalse (True, False) (False, True) p = absurd p
dmJoinFalse (True, False) (True, False) p = absurd p
dmJoinFalse (True, False) (True, True) p = absurd p
dmJoinFalse (True, True) (False, False) p = absurd p
dmJoinFalse (True, True) (False, True) p = absurd p
dmJoinFalse (True, True) (True, False) p = absurd p
dmJoinFalse (True, True) (True, True) p = absurd p

dmJoinTrue : (x, y : DM) ->
  ((x == (True, True)) || (y == (True, True))) = True ->
  (dmJoin x y == (True, True)) = True
dmJoinTrue (False, False) (False, False) p = absurd p
dmJoinTrue (False, False) (False, True) p = absurd p
dmJoinTrue (False, False) (True, False) p = absurd p
dmJoinTrue (False, False) (True, True) p = Refl
dmJoinTrue (False, True) (False, False) p = absurd p
dmJoinTrue (False, True) (False, True) p = absurd p
dmJoinTrue (False, True) (True, False) p = absurd p
dmJoinTrue (False, True) (True, True) p = Refl
dmJoinTrue (True, False) (False, False) p = absurd p
dmJoinTrue (True, False) (False, True) p = absurd p
dmJoinTrue (True, False) (True, False) p = absurd p
dmJoinTrue (True, False) (True, True) p = Refl
dmJoinTrue (True, True) (False, False) p = Refl
dmJoinTrue (True, True) (False, True) p = Refl
dmJoinTrue (True, True) (True, False) p = Refl
dmJoinTrue (True, True) (True, True) p = Refl

||| Endpoint extraction is sufficient in the actual solver pair model.
public export
dmScopedEndpointSound : (env : List (Fin n, DM)) -> (r : ScopedInterval n) -> (b : Bool) ->
  faceAt env (scopedEndpoint r b) = True -> (evalDM env r == (b, b)) = True
dmScopedEndpointSound env Zero False p = Refl
dmScopedEndpointSound env Zero True Refl impossible
dmScopedEndpointSound env One False Refl impossible
dmScopedEndpointSound env One True p = Refl
dmScopedEndpointSound env (Var i) b p = p
dmScopedEndpointSound env (Reverse x) b p = dmReverseEndpoint (evalDM env x) b (dmScopedEndpointSound env x (not b) p)
dmScopedEndpointSound env (Meet x y) False p =
  dmMeetFalse (evalDM env x) (evalDM env y) $
  soToEq $ case soOr (eqToSo p) of
    Left px => orSo (Left (eqToSo (dmScopedEndpointSound env x False (soToEq px))))
    Right py => orSo (Right (eqToSo (dmScopedEndpointSound env y False (soToEq py))))
dmScopedEndpointSound env (Meet x y) True p =
  let (px, py) = soAnd (eqToSo p) in
  dmMeetTrue (evalDM env x) (evalDM env y) $
    soToEq (andSo (eqToSo (dmScopedEndpointSound env x True (soToEq px)), eqToSo (dmScopedEndpointSound env y True (soToEq py))))
dmScopedEndpointSound env (Join x y) False p =
  let (px, py) = soAnd (eqToSo p) in
  dmJoinFalse (evalDM env x) (evalDM env y) $
    soToEq (andSo (eqToSo (dmScopedEndpointSound env x False (soToEq px)), eqToSo (dmScopedEndpointSound env y False (soToEq py))))
dmScopedEndpointSound env (Join x y) True p =
  dmJoinTrue (evalDM env x) (evalDM env y) $
  soToEq $ case soOr (eqToSo p) of
    Left px => orSo (Left (eqToSo (dmScopedEndpointSound env x True (soToEq px))))
    Right py => orSo (Right (eqToSo (dmScopedEndpointSound env y True (soToEq py))))

pairMeetOne : (x : DM) -> dmMeet x (True, True) = x
pairMeetOne (False, False) = Refl
pairMeetOne (False, True) = Refl
pairMeetOne (True, False) = Refl
pairMeetOne (True, True) = Refl

||| Meeting any solver value with one preserves it.
public export
dmMeetOne : (x : DM) -> dmMeet x (True, True) = x
dmMeetOne = pairMeetOne

dmMeetRightEndpoint : (x, y : DM) -> (y == (True, True)) = True -> dmMeet x y = x
dmMeetRightEndpoint (False, False) (False, False) p = absurd p
dmMeetRightEndpoint (False, True) (False, False) p = absurd p
dmMeetRightEndpoint (True, False) (False, False) p = absurd p
dmMeetRightEndpoint (True, True) (False, False) p = absurd p
dmMeetRightEndpoint (False, False) (False, True) p = absurd p
dmMeetRightEndpoint (False, True) (False, True) p = absurd p
dmMeetRightEndpoint (True, False) (False, True) p = absurd p
dmMeetRightEndpoint (True, True) (False, True) p = absurd p
dmMeetRightEndpoint (False, False) (True, False) p = absurd p
dmMeetRightEndpoint (False, True) (True, False) p = absurd p
dmMeetRightEndpoint (True, False) (True, False) p = absurd p
dmMeetRightEndpoint (True, True) (True, False) p = absurd p
dmMeetRightEndpoint (False, False) (True, True) p = Refl
dmMeetRightEndpoint (False, True) (True, True) p = Refl
dmMeetRightEndpoint (True, False) (True, True) p = Refl
dmMeetRightEndpoint (True, True) (True, True) p = Refl

||| The meet-one equivalence holds under an extracted one-endpoint face.
public export
dmMeetScopedOne : (env : List (Fin n, DM)) -> (x, y : ScopedInterval n) ->
  faceAt env (scopedEndpoint y True) = True -> evalDM env (Meet x y) = evalDM env x
dmMeetScopedOne env x y p = dmMeetRightEndpoint (evalDM env x) (evalDM env y)
  (dmScopedEndpointSound env y True p)

-- Agreement is only required for names actually read by an expression.
public export
DMLookupAgrees : {n : Nat} -> List (Fin n) -> List (Fin n, DM) -> List (Fin n, DM) -> Type
DMLookupAgrees {n} names left right = (i : Fin n) -> Elem i names -> lookupDM i left = lookupDM i right

leftAgreement : {xs : List (Fin n)} -> DMLookupAgrees (xs ++ ys) env1 env2 -> DMLookupAgrees xs env1 env2
leftAgreement {xs = []} agree i p impossible
leftAgreement {xs = i :: xs} agree i Here = agree i Here
leftAgreement {xs = x :: xs} agree i (There p) = leftAgreement (\j, q => agree j (There q)) i p

rightAgreement : (xs : List (Fin n)) -> DMLookupAgrees (xs ++ ys) env1 env2 -> DMLookupAgrees ys env1 env2
rightAgreement [] agree = agree
rightAgreement (_ :: xs) agree = rightAgreement xs (\j, q => agree j (There q))

||| Evaluation depends only on lookup results for the collected interval names.
public export
evalDMLocal : (r : ScopedInterval n) -> (left, right : List (Fin n, DM)) ->
  DMLookupAgrees (intervalNames r) left right -> evalDM left r = evalDM right r
evalDMLocal Zero left right agree = Refl
evalDMLocal One left right agree = Refl
evalDMLocal (Var i) left right agree = agree i Here
evalDMLocal (Reverse x) left right agree = cong dmReverse (evalDMLocal x left right agree)
evalDMLocal (Meet x y) left right agree =
  rewrite evalDMLocal x left right (leftAgreement agree) in
  rewrite evalDMLocal y left right (rightAgreement (intervalNames x) agree) in Refl
evalDMLocal (Join x y) left right agree =
  rewrite evalDMLocal x left right (leftAgreement agree) in
  rewrite evalDMLocal y left right (rightAgreement (intervalNames x) agree) in Refl

||| Face evaluation depends only on lookup results for the collected face names.
public export
faceAtLocal : (face : ScopedFace n) -> (left, right : List (Fin n, DM)) ->
  DMLookupAgrees (faceNames face) left right -> faceAt left face = faceAt right face
faceAtLocal SBottom left right agree = Refl
faceAtLocal STop left right agree = Refl
faceAtLocal (SEndpoint i b) left right agree = cong (\v => v == (b, b)) (agree i Here)
faceAtLocal (SConjunction x y) left right agree =
  rewrite faceAtLocal x left right (leftAgreement agree) in
  rewrite faceAtLocal y left right (rightAgreement (faceNames x) agree) in Refl
faceAtLocal (SDisjunction x y) left right agree =
  rewrite faceAtLocal x left right (leftAgreement agree) in
  rewrite faceAtLocal y left right (rightAgreement (faceNames x) agree) in Refl

||| Construct the branch selected by a total valuation for a name list.
public export
assignmentBranch : (names : List (Fin n)) -> (env : List (Fin n, DM)) ->
  (valuation : Fin n -> DM) -> List (Fin n, DM)
assignmentBranch [] env valuation = env
assignmentBranch (i :: rest) env valuation = assignmentBranch rest ((i, valuation i) :: env) valuation

allFourChoice : (p : DM -> Bool) -> (v : DM) ->
  all p [(False, False), (False, True), (True, False), (True, True)] = True -> p v = True
allFourChoice p (False, False) pr = soToEq (fst (soAnd (fst (soAnd (fst (soAnd (eqToSo pr)))))))
allFourChoice p (False, True) pr = soToEq (snd (soAnd (fst (soAnd (fst (soAnd (eqToSo pr)))))))
allFourChoice p (True, False) pr = soToEq (snd (soAnd (fst (soAnd (eqToSo pr)))))
allFourChoice p (True, True) pr = soToEq (snd (soAnd (eqToSo pr)))

||| Enumeration checks the leaf selected by every total valuation, even when
||| the input name list contains duplicates.
public export
allAssignmentsBranch : (names : List (Fin n)) -> (env : List (Fin n, DM)) ->
  (valuation : Fin n -> DM) -> (face : ScopedFace n) -> (r, s : ScopedInterval n) ->
  allAssignments names env face r s = True ->
  (not (faceAt (assignmentBranch names env valuation) face) ||
    evalDM (assignmentBranch names env valuation) r == evalDM (assignmentBranch names env valuation) s) = True
allAssignmentsBranch [] env valuation face r s pr = pr
allAssignmentsBranch (i :: rest) env valuation face r s pr =
  allAssignmentsBranch rest ((i, valuation i) :: env) valuation face r s
    (allFourChoice (\v => allAssignments rest ((i, v) :: env) face r s) (valuation i) pr)

finEqTrue : (i, j : Fin n) -> (i == j) = True -> i = j
finEqTrue FZ FZ pr = Refl
finEqTrue FZ (FS j) pr = absurd pr
finEqTrue (FS i) FZ pr = absurd pr
finEqTrue (FS i) (FS j) pr = cong FS (finEqTrue i j pr)

finEqSelf : (i : Fin n) -> (i == i) = True
finEqSelf FZ = Refl
finEqSelf (FS i) = finEqSelf i

lookupConsValuation : (i, j : Fin n) -> (valuation : Fin n -> DM) -> (env : List (Fin n, DM)) ->
  lookupDM i env = valuation i -> lookupDM i ((j, valuation j) :: env) = valuation i
lookupConsValuation i j valuation env pr with (i == j) proof eq
  lookupConsValuation i j valuation env pr | False = pr
  lookupConsValuation i j valuation env pr | True = cong valuation (sym (finEqTrue i j eq))

branchPreservesLookup : (names : List (Fin n)) -> (i : Fin n) -> (env : List (Fin n, DM)) ->
  (valuation : Fin n -> DM) -> lookupDM i env = valuation i ->
  lookupDM i (assignmentBranch names env valuation) = valuation i
branchPreservesLookup [] i env valuation pr = pr
branchPreservesLookup (j :: rest) i env valuation pr =
  branchPreservesLookup rest i ((j, valuation j) :: env) valuation
    (lookupConsValuation i j valuation env pr)

||| Every listed name has its valuation at the selected branch. Duplicate names
||| are harmless because each occurrence inserts the same valuation.
public export
assignmentBranchLookup : (names : List (Fin n)) -> (i : Fin n) -> Elem i names ->
  (env : List (Fin n, DM)) -> (valuation : Fin n -> DM) ->
  lookupDM i (assignmentBranch names env valuation) = valuation i
assignmentBranchLookup (i :: rest) i Here env valuation =
  branchPreservesLookup rest i ((i, valuation i) :: env) valuation
    (rewrite finEqSelf i in Refl)
assignmentBranchLookup (j :: rest) i (There pr) env valuation =
  assignmentBranchLookup rest i pr ((j, valuation j) :: env) valuation

trueFaceResult : (f, e : Bool) -> (not f || e) = True -> f = True -> e = True
trueFaceResult True e pr Refl = pr
trueFaceResult False e pr Refl impossible

||| Conditional soundness for an environment whose relevant lookup results
||| agree with the valuation-selected branch. Name coverage supplies these
||| hypotheses, but is not assumed here to follow from nub.
public export
allAssignmentsSoundOnAgreement :
  (names : List (Fin n)) -> (initial, target : List (Fin n, DM)) ->
  (valuation : Fin n -> DM) -> (face : ScopedFace n) -> (r, s : ScopedInterval n) ->
  DMLookupAgrees (faceNames face) (assignmentBranch names initial valuation) target ->
  DMLookupAgrees (intervalNames r) (assignmentBranch names initial valuation) target ->
  DMLookupAgrees (intervalNames s) (assignmentBranch names initial valuation) target ->
  allAssignments names initial face r s = True -> faceAt target face = True ->
  (evalDM target r == evalDM target s) = True
allAssignmentsSoundOnAgreement names initial target valuation face r s af ar as checked holds =
  trueFaceResult (faceAt target face) (evalDM target r == evalDM target s)
    (rewrite sym (faceAtLocal face (assignmentBranch names initial valuation) target af) in
     rewrite sym (evalDMLocal r (assignmentBranch names initial valuation) target ar) in
     rewrite sym (evalDMLocal s (assignmentBranch names initial valuation) target as) in
       allAssignmentsBranch names initial valuation face r s checked) holds

||| Pair-model interval semantics for an arbitrary total valuation.
public export
evalDMVal : (Fin n -> DM) -> ScopedInterval n -> DM
evalDMVal valuation Zero = (False, False)
evalDMVal valuation One = (True, True)
evalDMVal valuation (Var i) = valuation i
evalDMVal valuation (Reverse x) = dmReverse (evalDMVal valuation x)
evalDMVal valuation (Meet x y) = dmMeet (evalDMVal valuation x) (evalDMVal valuation y)
evalDMVal valuation (Join x y) = dmJoin (evalDMVal valuation x) (evalDMVal valuation y)

||| Pair-model face semantics for an arbitrary total valuation.
public export
faceAtVal : (Fin n -> DM) -> ScopedFace n -> Bool
faceAtVal valuation SBottom = False
faceAtVal valuation STop = True
faceAtVal valuation (SEndpoint i b) = valuation i == (b, b)
faceAtVal valuation (SConjunction x y) = faceAtVal valuation x && faceAtVal valuation y
faceAtVal valuation (SDisjunction x y) = faceAtVal valuation x || faceAtVal valuation y

public export
DMValAgrees : {n : Nat} -> List (Fin n) -> List (Fin n, DM) -> (Fin n -> DM) -> Type
DMValAgrees {n} names env valuation = (i : Fin n) -> Elem i names -> lookupDM i env = valuation i

valLeft : {xs : List (Fin n)} -> DMValAgrees (xs ++ ys) env valuation -> DMValAgrees xs env valuation
valLeft {xs = []} agree i p impossible
valLeft {xs = i :: xs} agree i Here = agree i Here
valLeft {xs = x :: xs} agree i (There p) = valLeft (\j, q => agree j (There q)) i p

valRight : (xs : List (Fin n)) -> DMValAgrees (xs ++ ys) env valuation -> DMValAgrees ys env valuation
valRight [] agree = agree
valRight (_ :: xs) agree = valRight xs (\j, q => agree j (There q))

||| Relate the solver evaluator to total-valuation semantics on its read names.
public export
evalDMValLocal : (r : ScopedInterval n) -> (env : List (Fin n, DM)) -> (valuation : Fin n -> DM) ->
  DMValAgrees (intervalNames r) env valuation -> evalDM env r = evalDMVal valuation r
evalDMValLocal Zero env valuation agree = Refl
evalDMValLocal One env valuation agree = Refl
evalDMValLocal (Var i) env valuation agree = agree i Here
evalDMValLocal (Reverse x) env valuation agree = cong dmReverse (evalDMValLocal x env valuation agree)
evalDMValLocal (Meet x y) env valuation agree =
  rewrite evalDMValLocal x env valuation (valLeft agree) in
  rewrite evalDMValLocal y env valuation (valRight (intervalNames x) agree) in Refl
evalDMValLocal (Join x y) env valuation agree =
  rewrite evalDMValLocal x env valuation (valLeft agree) in
  rewrite evalDMValLocal y env valuation (valRight (intervalNames x) agree) in Refl

||| Relate the solver face evaluator to total-valuation semantics on its read names.
public export
faceAtValLocal : (face : ScopedFace n) -> (env : List (Fin n, DM)) -> (valuation : Fin n -> DM) ->
  DMValAgrees (faceNames face) env valuation -> faceAt env face = faceAtVal valuation face
faceAtValLocal SBottom env valuation agree = Refl
faceAtValLocal STop env valuation agree = Refl
faceAtValLocal (SEndpoint i b) env valuation agree = cong (\v => v == (b, b)) (agree i Here)
faceAtValLocal (SConjunction x y) env valuation agree =
  rewrite faceAtValLocal x env valuation (valLeft agree) in
  rewrite faceAtValLocal y env valuation (valRight (faceNames x) agree) in Refl
faceAtValLocal (SDisjunction x y) env valuation agree =
  rewrite faceAtValLocal x env valuation (valLeft agree) in
  rewrite faceAtValLocal y env valuation (valRight (faceNames x) agree) in Refl

||| Soundness of enumeration given explicit coverage of all read names.
public export
allAssignmentsValSound : (names : List (Fin n)) -> (initial : List (Fin n, DM)) ->
  (valuation : Fin n -> DM) -> (face : ScopedFace n) -> (r, s : ScopedInterval n) ->
  ((i : Fin n) -> Elem i (faceNames face) -> Elem i names) ->
  ((i : Fin n) -> Elem i (intervalNames r) -> Elem i names) ->
  ((i : Fin n) -> Elem i (intervalNames s) -> Elem i names) ->
  allAssignments names initial face r s = True -> faceAtVal valuation face = True ->
  (evalDMVal valuation r == evalDMVal valuation s) = True
allAssignmentsValSound names initial valuation face r s cf cr cs checked holds =
  trueFaceResult (faceAtVal valuation face) (evalDMVal valuation r == evalDMVal valuation s)
    (rewrite sym (faceAtValLocal face (assignmentBranch names initial valuation) valuation
      (\i, p => assignmentBranchLookup names i (cf i p) initial valuation)) in
     rewrite sym (evalDMValLocal r (assignmentBranch names initial valuation) valuation
      (\i, p => assignmentBranchLookup names i (cr i p) initial valuation)) in
     rewrite sym (evalDMValLocal s (assignmentBranch names initial valuation) valuation
      (\i, p => assignmentBranchLookup names i (cs i p) initial valuation)) in
       allAssignmentsBranch names initial valuation face r s checked) holds

||| Admission can only return Accepted when the actual enumeration returned true.
public export
restrictedIntervalEqualChecked : {n : Nat} -> (budget : Nat) -> (face : ScopedFace n) ->
  (r, s : ScopedInterval n) -> restrictedIntervalEqual budget face r s = Accepted ->
  intervalEqual face r s = True
restrictedIntervalEqualChecked {n} budget face r s accepted with (not (n <= 12))
  restrictedIntervalEqualChecked {n} budget face r s Refl | True impossible
  restrictedIntervalEqualChecked {n} budget face r s accepted | False with
    (faceNodes (min 12 budget) face >>= \f => intervalNodes f r >>= \g => intervalNodes g s)
    restrictedIntervalEqualChecked {n} budget face r s Refl | False | Nothing impossible
    restrictedIntervalEqualChecked {n} budget face r s accepted | False | Just remaining with (intervalEqual face r s) proof eq
      restrictedIntervalEqualChecked {n} budget face r s Refl | False | Just remaining | False impossible
      restrictedIntervalEqualChecked {n} budget face r s accepted | False | Just remaining | True = Refl

pairEqTrue : (x, y : DM) -> (x == y) = True -> x = y
pairEqTrue (False, False) (False, False) pr = Refl
pairEqTrue (False, False) (False, True) pr = absurd pr
pairEqTrue (False, False) (True, False) pr = absurd pr
pairEqTrue (False, False) (True, True) pr = absurd pr
pairEqTrue (False, True) (False, False) pr = absurd pr
pairEqTrue (False, True) (False, True) pr = Refl
pairEqTrue (False, True) (True, False) pr = absurd pr
pairEqTrue (False, True) (True, True) pr = absurd pr
pairEqTrue (True, False) (False, False) pr = absurd pr
pairEqTrue (True, False) (False, True) pr = absurd pr
pairEqTrue (True, False) (True, False) pr = Refl
pairEqTrue (True, False) (True, True) pr = absurd pr
pairEqTrue (True, True) (False, False) pr = absurd pr
pairEqTrue (True, True) (False, True) pr = absurd pr
pairEqTrue (True, True) (True, False) pr = absurd pr
pairEqTrue (True, True) (True, True) pr = Refl

appendElemLeft : (xs : List a) -> Elem i xs -> Elem i (xs ++ ys)
appendElemLeft (i :: xs) Here = Here
appendElemLeft (x :: xs) (There pr) = There (appendElemLeft xs pr)

appendElemRight : (xs : List a) -> Elem i ys -> Elem i (xs ++ ys)
appendElemRight [] pr = pr
appendElemRight (x :: xs) pr = There (appendElemRight xs pr)

||| Accepted conversion is sound for any total valuation, assuming the names
||| surviving the actual nub cover each name read by the three expressions.
public export
restrictedIntervalEqualValSoundGivenCoverage : {n : Nat} ->
  (budget : Nat) -> (face : ScopedFace n) -> (r, s : ScopedInterval n) ->
  (valuation : Fin n -> DM) ->
  ((i : Fin n) -> Elem i (faceNames face ++ intervalNames r ++ intervalNames s) ->
    Elem i (nub (faceNames face ++ intervalNames r ++ intervalNames s))) ->
  restrictedIntervalEqual budget face r s = Accepted -> faceAtVal valuation face = True ->
  evalDMVal valuation r = evalDMVal valuation s
restrictedIntervalEqualValSoundGivenCoverage budget face r s valuation cover accepted holds =
  pairEqTrue (evalDMVal valuation r) (evalDMVal valuation s) $
  allAssignmentsValSound (nub (faceNames face ++ intervalNames r ++ intervalNames s)) [] valuation face r s
    (\i, p => cover i (appendElemLeft (faceNames face) p))
    (\i, p => cover i (appendElemRight (faceNames face) (appendElemLeft (intervalNames r) p)))
    (\i, p => cover i (appendElemRight (faceNames face) (appendElemRight (intervalNames r) p)))
    (restrictedIntervalEqualChecked budget face r s accepted) holds

-- Data.List.nubBy's accumulator is a nested library definition. Resolve that
-- exact worker for proof only; selection fails closed if the library changes.
-- The solver itself still calls Data.List.nub unchanged.
nubWorker : {a : Type} -> List a -> (a -> a -> Bool) -> List a -> List a
nubWorker {a} = %runElab do
  names <- getReferredFns `{Data.List.nubBy}
  case filter (\name => case name of NS _ (Nested _ (UN (Basic "nubBy'"))) => True; _ => False) names of
    [name] => do
      ty <- quote a
      check (IApp EmptyFC (IVar EmptyFC name) ty)
    _ => fail "Data.List.nubBy accumulator not uniquely found"

foldAnyFinMember : (i : Fin n) -> (xs : List (Fin n)) -> (seed : Bool) ->
  foldl (\b, j => b || i == j) seed xs = True -> Either (seed = True) (Elem i xs)
foldAnyFinMember i [] seed pr = Left pr
foldAnyFinMember i (x :: xs) seed pr =
  case foldAnyFinMember i xs (seed || i == x) pr of
    Right inTail => Right (There inTail)
    Left prev => case soOr (eqToSo prev) of
      Left seedTrue => Left (soToEq seedTrue)
      Right equal => case finEqTrue i x (soToEq equal) of
        Refl => Right Here

finElemBySound : (i : Fin n) -> (xs : List (Fin n)) -> elemBy (==) i xs = True -> Elem i xs
finElemBySound i xs pr =
  case foldAnyFinMember i xs False pr of
    Left impossibleSeed => absurd impossibleSeed
    Right member => member

nubWorkerCoverage : (acc, xs : List (Fin n)) -> (i : Fin n) -> Elem i xs ->
  Either (Elem i acc) (Elem i (nubWorker acc (==) xs))
nubWorkerCoverage acc (i :: xs) i Here with (elemBy (==) i acc) proof seen
  nubWorkerCoverage acc (i :: xs) i Here | True = Left (finElemBySound i acc seen)
  nubWorkerCoverage acc (i :: xs) i Here | False =
    Right Here
nubWorkerCoverage acc (x :: xs) i (There member) with (elemBy (==) x acc) proof seen
  nubWorkerCoverage acc (x :: xs) i (There member) | True =
    case nubWorkerCoverage acc xs i member of
      Left inAcc => Left inAcc
      Right inResult => Right inResult
  nubWorkerCoverage acc (x :: xs) i (There member) | False =
    case nubWorkerCoverage (x :: acc) xs i member of
      Left Here => Right Here
      Left (There inAcc) => Left inAcc
      Right inResult => Right (There inResult)

||| `Data.List.nub` retains every Fin name, including when names repeat.
public export
finNubCoverage : (xs : List (Fin n)) -> (i : Fin n) -> Elem i xs -> Elem i (nub xs)
finNubCoverage xs i member = case nubWorkerCoverage [] xs i member of
  Left inEmpty => absurd inEmpty
  Right inResult => inResult

||| An Accepted restricted comparison is sound for every total pair-model
||| valuation satisfying the face. This is not free-algebra or CCHM soundness.
public export
restrictedIntervalEqualValSound : {n : Nat} ->
  (budget : Nat) -> (face : ScopedFace n) -> (r, s : ScopedInterval n) ->
  (valuation : Fin n -> DM) ->
  restrictedIntervalEqual budget face r s = Accepted -> faceAtVal valuation face = True ->
  evalDMVal valuation r = evalDMVal valuation s
restrictedIntervalEqualValSound budget face r s valuation accepted holds =
  restrictedIntervalEqualValSoundGivenCoverage budget face r s valuation
    (\i, member => finNubCoverage (faceNames face ++ intervalNames r ++ intervalNames s) i member)
    accepted holds

||| Evaluate the reference Nat-labelled interval syntax in the solver's actual
||| four-pair algebra. This is not the separate diamond in FaceSoundness.
public export
evalReferenceDM : (Nat -> DM) -> Interval Nat -> DM
evalReferenceDM env Zero = (False, False)
evalReferenceDM env One = (True, True)
evalReferenceDM env (Var i) = env i
evalReferenceDM env (Reverse x) = dmReverse (evalReferenceDM env x)
evalReferenceDM env (Meet x y) = dmMeet (evalReferenceDM env x) (evalReferenceDM env y)
evalReferenceDM env (Join x y) = dmJoin (evalReferenceDM env x) (evalReferenceDM env y)

||| Evaluation commutes with the existing scope-forgetting map, for every
||| reference valuation and every scoped interval, including reversals.
public export
forgetIntervalDM : (env : Nat -> DM) -> (r : ScopedInterval n) ->
  evalReferenceDM env (forgetInterval r) = evalDMVal (env . Data.Fin.finToNat) r
forgetIntervalDM env Zero = Refl
forgetIntervalDM env One = Refl
forgetIntervalDM env (Var i) = Refl
forgetIntervalDM env (Reverse x) = cong dmReverse (forgetIntervalDM env x)
forgetIntervalDM env (Meet x y) =
  rewrite forgetIntervalDM env x in rewrite forgetIntervalDM env y in Refl
forgetIntervalDM env (Join x y) =
  rewrite forgetIntervalDM env x in rewrite forgetIntervalDM env y in Refl

||| Reference face syntax interpreted by exact endpoint equality in the pair model.
public export
faceReferenceDM : (Nat -> DM) -> Face -> Bool
faceReferenceDM env Bottom = False
faceReferenceDM env Top = True
faceReferenceDM env (Endpoint i b) = env i == (b, b)
faceReferenceDM env (Conjunction x y) = faceReferenceDM env x && faceReferenceDM env y
faceReferenceDM env (Disjunction x y) = faceReferenceDM env x || faceReferenceDM env y

||| Scope forgetting preserves endpoint assumptions, conjunction and disjunction.
public export
forgetFaceDM : (env : Nat -> DM) -> (face : ScopedFace n) ->
  faceReferenceDM env (forgetFace face) = faceAtVal (env . Data.Fin.finToNat) face
forgetFaceDM env SBottom = Refl
forgetFaceDM env STop = Refl
forgetFaceDM env (SEndpoint i b) = Refl
forgetFaceDM env (SConjunction x y) =
  rewrite forgetFaceDM env x in rewrite forgetFaceDM env y in Refl
forgetFaceDM env (SDisjunction x y) =
  rewrite forgetFaceDM env x in rewrite forgetFaceDM env y in Refl

||| Accepted restricted comparison implies equality of the forgotten reference
||| expressions in the pair model under every satisfying reference valuation.
public export
restrictedReferenceDMSound : {n : Nat} -> (budget : Nat) ->
  (face : ScopedFace n) -> (r, s : ScopedInterval n) -> (env : Nat -> DM) ->
  restrictedIntervalEqual budget face r s = Accepted ->
  faceReferenceDM env (forgetFace face) = True ->
  evalReferenceDM env (forgetInterval r) = evalReferenceDM env (forgetInterval s)
restrictedReferenceDMSound budget face r s env accepted holds =
  trans (forgetIntervalDM env r) $
  trans (restrictedIntervalEqualValSound budget face r s (env . Data.Fin.finToNat)
    accepted (trans (sym (forgetFaceDM env face)) holds)) (sym (forgetIntervalDM env s))

||| Encode independent positive and negative Boolean generator observations.
public export
signedDM : Bool -> Bool -> DM
signedDM positive negative = (positive, not negative)

||| Reversal exchanges the two signed observations.
public export
signedDMReverse : (p, q : Bool) ->
  dmReverse (signedDM p q) = signedDM q p
signedDMReverse False False = Refl
signedDMReverse False True = Refl
signedDMReverse True False = Refl
signedDMReverse True True = Refl

||| Coordinate law for signed observations of meet.
public export
signedDMMeet : (p, q, r, s : Bool) ->
  dmMeet (signedDM p q) (signedDM r s) = signedDM (p && r) (q || s)
signedDMMeet False False False False = Refl
signedDMMeet False False False True = Refl
signedDMMeet False False True False = Refl
signedDMMeet False False True True = Refl
signedDMMeet False True False False = Refl
signedDMMeet False True False True = Refl
signedDMMeet False True True False = Refl
signedDMMeet False True True True = Refl
signedDMMeet True False False False = Refl
signedDMMeet True False False True = Refl
signedDMMeet True False True False = Refl
signedDMMeet True False True True = Refl
signedDMMeet True True False False = Refl
signedDMMeet True True False True = Refl
signedDMMeet True True True False = Refl
signedDMMeet True True True True = Refl

||| Coordinate law for signed observations of join.
public export
signedDMJoin : (p, q, r, s : Bool) ->
  dmJoin (signedDM p q) (signedDM r s) = signedDM (p || r) (q && s)
signedDMJoin False False False False = Refl
signedDMJoin False False False True = Refl
signedDMJoin False False True False = Refl
signedDMJoin False False True True = Refl
signedDMJoin False True False False = Refl
signedDMJoin False True False True = Refl
signedDMJoin False True True False = Refl
signedDMJoin False True True True = Refl
signedDMJoin True False False False = Refl
signedDMJoin True False False True = Refl
signedDMJoin True False True False = Refl
signedDMJoin True False True True = Refl
signedDMJoin True True False False = Refl
signedDMJoin True True False True = Refl
signedDMJoin True True True False = Refl
signedDMJoin True True True True = Refl

||| The independent signed interpretation is exactly the four-pair model.
public export
evalSignedReferenceDM : (env : SignedAssignment) -> (x : Interval Nat) ->
  evalReferenceDM (\n => signedDM (env n False) (env n True)) x =
    signedDM (evalSigned env False x) (evalSigned env True x)
evalSignedReferenceDM env Zero = Refl
evalSignedReferenceDM env One = Refl
evalSignedReferenceDM env (Var n) = Refl
evalSignedReferenceDM env (Reverse x) =
  rewrite evalSignedReferenceDM env x in
  signedDMReverse (evalSigned env False x) (evalSigned env True x)
evalSignedReferenceDM env (Meet x y) =
  rewrite evalSignedReferenceDM env x in
  rewrite evalSignedReferenceDM env y in
  signedDMMeet (evalSigned env False x) (evalSigned env True x)
    (evalSigned env False y) (evalSigned env True y)
evalSignedReferenceDM env (Join x y) =
  rewrite evalSignedReferenceDM env x in
  rewrite evalSignedReferenceDM env y in
  signedDMJoin (evalSigned env False x) (evalSigned env True x)
    (evalSigned env False y) (evalSigned env True y)
