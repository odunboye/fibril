-- A bounded checker for abstract size-change graph certificates.
-- These graphs are untrusted and are not connected to source or core calls.
module Fibril.Termination.SizeChange

import Data.List
import Data.Maybe

%default total

||| A relation from an argument before a call to an argument after it.
||| Unknown asserts no ordering; NonIncreasing asserts <=; Decreases asserts <.
public export
data Relation = Unknown | NonIncreasing | Decreases

public export
Eq Relation where
  Unknown == Unknown = True
  NonIncreasing == NonIncreasing = True
  Decreases == Decreases = True
  _ == _ = False

||| Rows are callee arguments; columns are caller arguments.
public export
record Call where
  constructor Edge
  caller : Nat
  callee : Nat
  matrix : List (List Relation)

public export
Eq Call where
  a == b = a.caller == b.caller && a.callee == b.callee && a.matrix == b.matrix

||| This result concerns the supplied abstract graph only. It is not authority
||| to accept a source definition, a core term, or an unverified call graph.
public export
data Verdict = GraphAccepted | GraphRejected String | GraphInconclusive String

||| Sequential relation: unknown dominates; strictness survives known chains.
public export
composeRelation : Relation -> Relation -> Relation
composeRelation Unknown _ = Unknown
composeRelation _ Unknown = Unknown
composeRelation Decreases _ = Decreases
composeRelation _ Decreases = Decreases
composeRelation NonIncreasing NonIncreasing = NonIncreasing

||| Alternative intermediate witnesses: retain the strongest known relation.
public export
bestRelation : Relation -> Relation -> Relation
bestRelation Decreases _ = Decreases
bestRelation _ Decreases = Decreases
bestRelation NonIncreasing _ = NonIncreasing
bestRelation _ NonIncreasing = NonIncreasing
bestRelation Unknown Unknown = Unknown

||| Short-circuit list-size admission, before matrix construction or closure.
within : Nat -> List a -> Bool
within Z [] = True
within Z (_ :: _) = False
within (S _) [] = True
within (S remaining) (_ :: rest) = within remaining rest

at : Nat -> List a -> Maybe a
at _ [] = Nothing
at Z (value :: _) = Just value
at (S index) (_ :: rest) = at index rest

indicesFrom : Nat -> Nat -> List Nat
indicesFrom _ Z = []
indicesFrom start (S count) = start :: indicesFrom (S start) count

indices : Nat -> List Nat
indices = indicesFrom 0

cell : Nat -> Nat -> List (List Relation) -> Relation
cell row column matrix = fromMaybe Unknown (at row matrix >>= at column)

||| Compose caller->middle followed by middle->callee. Shape checks must occur
||| before using this internal operation on untrusted matrices.
compose : List Nat -> Call -> Call -> Maybe Call
compose arities first second = do
  if first.callee == second.caller then Just () else Nothing
  source <- at first.caller arities
  middle <- at first.callee arities
  target <- at second.callee arities
  let relation : Nat -> Nat -> Relation
      relation row column = foldl bestRelation Unknown
        (map (\k => composeRelation (cell k column first.matrix) (cell row k second.matrix)) (indices middle))
  Just (Edge first.caller second.callee (map (\row => map (relation row) (indices source)) (indices target)))

shape : List Nat -> Call -> Bool
shape arities edge = case (at edge.caller arities, at edge.callee arities) of
  (Just source, Just target) =>
    within 8 edge.matrix && all (within 8) edge.matrix &&
    length edge.matrix == target && all (\row => length row == source) edge.matrix
  _ => False

duplicates : Eq a => List a -> Bool
duplicates [] = False
duplicates (x :: xs) = elem x xs || duplicates xs

strictDiagonal : List Nat -> Call -> Bool
strictDiagonal arities edge = case at edge.caller arities of
  Nothing => False
  Just count => any (\i => cell i i edge.matrix == Decreases) (indices count)

closedPair : List Nat -> List Call -> Call -> Call -> Bool
closedPair arities certificate first second = case compose arities first second of
  Nothing => True
  Just result => elem result certificate

safeIdempotent : List Nat -> Call -> Bool
safeIdempotent arities edge =
  if edge.caller /= edge.callee then True else case compose arities edge edge of
    Just result => result /= edge || strictDiagonal arities edge
    Nothing => False

-- Shared input admission is repeated when a produced certificate is checked.
inputAdmission : List Nat -> List Call -> Maybe Verdict
inputAdmission arities direct =
  if not (within 16 arities) then Just (GraphInconclusive "function-count admission exhausted (16)") else
  if not (all (<= 8) arities) then Just (GraphInconclusive "argument-count admission exhausted (8)") else
  if not (within 128 direct) then Just (GraphInconclusive "direct-call admission exhausted (128)") else Nothing

||| Verify a proposed finite closure for an abstract graph. Accepted means:
||| every direct edge is included, the supplied set is closed under composition,
||| and every idempotent self-cycle has a strict diagonal. No call extraction,
||| recursive core, or source acceptance is implemented here.
|||
||| Caps are admission policies, not hard time, memory or stack guarantees.
public export
verify : List Nat -> List Call -> List Call -> Verdict
verify arities direct certificate = case inputAdmission arities direct of
  Just verdict => verdict
  Nothing =>
    if not (within 32 certificate) then GraphInconclusive "certificate admission exhausted (32)" else
    if not (all (shape arities) direct && all (shape arities) certificate)
      then GraphRejected "edge endpoint or matrix shape is invalid" else
    if duplicates certificate then GraphRejected "certificate contains duplicate edges" else
    if not (all (\edge => elem edge certificate) direct)
      then GraphRejected "certificate omits a direct call" else
    if not (all (\first => all (closedPair arities certificate first) certificate) certificate)
      then GraphRejected "certificate is not closed under composition" else
    if not (all (safeIdempotent arities) certificate)
      then GraphRejected "an idempotent cycle has no strict diagonal" else GraphAccepted

||| A producer result is not authority for source or core termination. A
||| completed candidate carries the verifier's actual verdict, including a
||| rejection of graphs that do not meet the cycle criterion.
public export
data Production = ClosureProduced (List Call) Verdict
                | ProductionInvalid String
                | ProductionInconclusive String

-- Preserve first-occurrence order; never retain a 33rd certificate edge.
addEdge : Call -> List Call -> Either String (List Call)
addEdge edge edges =
  if elem edge edges then Right edges else
    if not (within 31 edges) then Left "certificate admission exhausted (32)"
      else Right (edges ++ [edge])

seed : List Call -> List Call -> Either String (List Call)
seed [] edges = Right edges
seed (edge :: rest) edges = do
  next <- addEdge edge edges
  seed rest next

addSecond : List Nat -> Call -> List Call -> List Call -> Either String (List Call)
addSecond arities first [] edges = Right edges
addSecond arities first (second :: rest) edges = do
  next <- case compose arities first second of
    Nothing => Right edges
    Just result => addEdge result edges
  addSecond arities first rest next

addFirst : List Nat -> List Call -> List Call -> List Call -> Either String (List Call)
addFirst arities [] snapshot edges = Right edges
addFirst arities (first :: rest) snapshot edges = do
  next <- addSecond arities first snapshot edges
  addFirst arities rest snapshot next

-- Each round examines an immutable snapshot. New edges participate in both
-- operand positions in later rounds. A stable round is checked independently.
produceRounds : Nat -> List Nat -> List Call -> List Call -> Production
produceRounds Z arities direct edges = ProductionInconclusive "closure round budget exhausted"
produceRounds (S fuel) arities direct edges = case addFirst arities edges edges edges of
  Left message => ProductionInconclusive message
  Right next => if next == edges
    then ClosureProduced next (verify arities direct next)
    else produceRounds fuel arities direct next

||| Produce a deterministic closure for the supplied abstract graph, then run
||| verify on the original direct graph and the candidate certificate. Fuel is
||| bounded to 33 rounds; exhaustion is inconclusive, not partial acceptance.
public export
produceWithFuel : Nat -> List Nat -> List Call -> Production
produceWithFuel fuel arities direct = case inputAdmission arities direct of
  Just (GraphInconclusive message) => ProductionInconclusive message
  Just (GraphRejected message) => ProductionInvalid message
  Just GraphAccepted => ProductionInvalid "unexpected graph admission verdict"
  Nothing =>
    if not (all (shape arities) direct) then ProductionInvalid "edge endpoint or matrix shape is invalid" else
    if fuel > 33 then ProductionInconclusive "closure round admission exhausted (33)" else
    case seed direct [] of
      Left message => ProductionInconclusive message
      Right initial => produceRounds fuel arities direct initial

||| At most 32 additions plus a final stable round fit the admitted certificate.
public export
produce : List Nat -> List Call -> Production
produce = produceWithFuel 33
