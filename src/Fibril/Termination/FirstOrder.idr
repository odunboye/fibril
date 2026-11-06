-- Standalone, first-order Nat-only prototype. Not Fibril source or core.
module Fibril.Termination.FirstOrder

import Data.List
import Fibril.Termination.SizeChange

%default total

||| A local Nat variable, or a Nat value whose origin is not tracked. Arguments
||| cannot themselves contain calls in this deliberately restricted fragment.
public export
data Argument = Local Nat | Unrelated

||| Explicit calls and exhaustive control flow. The successor arm of CaseNat
||| introduces the predecessor as local 0; existing locals shift by one.
||| There is no indirect call, hidden expression, partial call, or source AST.
public export
data Body = End
          | Direct Nat (List Argument)
          | Both Body Body
          | Choice Body Body
          | CaseNat Nat Body Body

||| Every input argument is a Nat. Function identity is its position in the
||| group. This representation has no result types or quantity judgments.
public export
record Function where
  constructor Definition
  arity : Nat
  body : Body

public export
data Problem = InvalidBody String | AdmissionExhausted String

within : Nat -> List a -> Bool
within Z [] = True
within Z (_ :: _) = False
within (S _) [] = True
within (S fuel) (_ :: rest) = within fuel rest

at : Nat -> List a -> Maybe a
at _ [] = Nothing
at Z (value :: _) = Just value
at (S index) (_ :: rest) = at index rest

indicesFrom : Nat -> Nat -> List Nat
indicesFrom _ Z = []
indicesFrom start (S count) = start :: indicesFrom (S start) count

||| Count the complete body tree and call sites before constructing graph edges.
||| Every admitted call argument list is separately bounded.
admitBody : Nat -> Nat -> Body -> Either Problem (Nat, Nat)
admitBody Z _ _ = Left (AdmissionExhausted "body-node admission exhausted (256)")
admitBody (S nodes) calls End = Right (nodes, calls)
admitBody (S nodes) Z (Direct _ _) = Left (AdmissionExhausted "call-site admission exhausted (128)")
admitBody (S nodes) (S calls) (Direct _ args) =
  if within 8 args then Right (nodes, calls) else Left (AdmissionExhausted "call-argument admission exhausted (8)")
admitBody (S nodes) calls (Both left right) = do
  (nodes, calls) <- admitBody nodes calls left
  admitBody nodes calls right
admitBody (S nodes) calls (Choice left right) = do
  (nodes, calls) <- admitBody nodes calls left
  admitBody nodes calls right
admitBody (S nodes) calls (CaseNat _ zero successor) = do
  (nodes, calls) <- admitBody nodes calls zero
  admitBody nodes calls successor

admitFunctions : Nat -> Nat -> List Function -> Either Problem ()
admitFunctions nodes calls [] = Right ()
admitFunctions nodes calls (definition :: rest) = do
  if definition.arity <= 8 then Right () else Left (AdmissionExhausted "function-argument admission exhausted (8)")
  (nodes, calls) <- admitBody nodes calls definition.body
  admitFunctions nodes calls rest

admit : List Function -> Either Problem ()
admit definitions = do
  if within 16 definitions then Right () else Left (AdmissionExhausted "function-count admission exhausted (16)")
  admitFunctions 256 128 definitions

-- Producer provenance is a row of relations to the caller's original inputs.
identityRows : Nat -> List (List Relation)
identityRows count = map (\i => map (\j => if i == j then NonIncreasing else Unknown) (indicesFrom 0 count)) (indicesFrom 0 count)

strictlySmaller : Relation -> Relation
strictlySmaller Unknown = Unknown
strictlySmaller NonIncreasing = Decreases
strictlySmaller Decreases = Decreases

argumentRow : Nat -> List (List Relation) -> Argument -> Either Problem (List Relation)
argumentRow width env (Local index) = case at index env of
  Just row => Right row
  Nothing => Left (InvalidBody "call argument references an out-of-scope local")
argumentRow width env Unrelated = Right (replicate width Unknown)

extractBody : List Function -> Nat -> Nat -> List (List Relation) -> Body -> List Call -> Either Problem (List Call)
extractBody definitions caller width env End edges = Right edges
extractBody definitions caller width env (Direct target args) edges = do
  callee <- case at target definitions of
    Nothing => Left (InvalidBody "call target is outside the function group")
    Just definition => Right definition
  if length args == callee.arity then Right () else Left (InvalidBody "call arity does not match its target")
  rows <- traverse (argumentRow width env) args
  Right (Edge caller target rows :: edges)
extractBody definitions caller width env (Both left right) edges = do
  edges <- extractBody definitions caller width env left edges
  extractBody definitions caller width env right edges
extractBody definitions caller width env (Choice left right) edges = do
  edges <- extractBody definitions caller width env left edges
  extractBody definitions caller width env right edges
extractBody definitions caller width env (CaseNat local zero successor) edges = do
  row <- case at local env of
    Nothing => Left (InvalidBody "Nat case references an out-of-scope local")
    Just row => Right row
  if within 15 env then Right () else Left (AdmissionExhausted "local-scope admission exhausted (16)")
  edges <- extractBody definitions caller width env zero edges
  extractBody definitions caller width (map strictlySmaller row :: env) successor edges

extractFunctions : List Function -> Nat -> List Function -> List Call -> Either Problem (List Call)
extractFunctions definitions caller [] edges = Right (reverse edges)
extractFunctions definitions caller (definition :: rest) edges = do
  edges <- extractBody definitions caller definition.arity (identityRows definition.arity) definition.body edges
  extractFunctions definitions (S caller) rest edges

||| Extract all direct call-site matrices from this Nat-only symbolic body.
||| Success is about this fragment only; it certifies no Fibril program.
public export
extract : List Function -> Either Problem (List Call)
extract definitions = do
  admit definitions
  extractFunctions definitions 0 definitions []

-- The independent body walk uses root/descendant provenance rather than the
-- producer's relation rows. Each local has at most one originating argument.
data Origin = Root Nat | Descendant Nat

descendant : Origin -> Origin
descendant (Root index) = Descendant index
descendant (Descendant index) = Descendant index

originRelation : Origin -> Nat -> Relation
originRelation (Root index) column = if index == column then NonIncreasing else Unknown
originRelation (Descendant index) column = if index == column then Decreases else Unknown

rowMatches : Nat -> List Origin -> Argument -> List Relation -> Bool
rowMatches width env (Local index) row = case at index env of
  Nothing => False
  Just origin => row == map (originRelation origin) (indicesFrom 0 width)
rowMatches width env Unrelated row = row == replicate width Unknown

checkBody : List Function -> Nat -> Nat -> List Origin -> Body -> List Call -> Either Problem (List Call)
checkBody definitions caller width env End edges = Right edges
checkBody definitions caller width env (Direct target args) [] = Left (InvalidBody "proposed graph omits a call site")
checkBody definitions caller width env (Direct target args) (edge :: edges) = do
  callee <- case at target definitions of
    Nothing => Left (InvalidBody "call target is outside the function group")
    Just definition => Right definition
  if length args == callee.arity then Right () else Left (InvalidBody "call arity does not match its target")
  if edge.caller == caller && edge.callee == target &&
     length edge.matrix == length args && all id (zipWith (rowMatches width env) args edge.matrix)
    then Right edges else Left (InvalidBody "proposed call edge does not match the body")
checkBody definitions caller width env (Both left right) edges = do
  edges <- checkBody definitions caller width env left edges
  checkBody definitions caller width env right edges
checkBody definitions caller width env (Choice left right) edges = do
  edges <- checkBody definitions caller width env left edges
  checkBody definitions caller width env right edges
checkBody definitions caller width env (CaseNat local zero successor) edges = do
  origin <- case at local env of
    Nothing => Left (InvalidBody "Nat case references an out-of-scope local")
    Just origin => Right origin
  if within 15 env then Right () else Left (AdmissionExhausted "local-scope admission exhausted (16)")
  edges <- checkBody definitions caller width env zero edges
  checkBody definitions caller width (descendant origin :: env) successor edges

checkFunctions : List Function -> Nat -> List Function -> List Call -> Either Problem (List Call)
checkFunctions definitions caller [] edges = Right edges
checkFunctions definitions caller (definition :: rest) edges = do
  edges <- checkBody definitions caller definition.arity (map Root (indicesFrom 0 definition.arity)) definition.body edges
  checkFunctions definitions (S caller) rest edges

||| Rewalk the exact symbolic bodies and compare every call in traversal order.
||| It does not trust a producer's relation rows, and does not inspect Fibril
||| source, core terms, runtime quantities, or an omitted external call.
public export
check : List Function -> List Call -> Either Problem ()
check definitions proposed = do
  admit definitions
  if within 128 proposed then Right () else Left (AdmissionExhausted "proposed-call admission exhausted (128)")
  if all (\edge => within 8 edge.matrix && all (within 8) edge.matrix) proposed
    then Right () else Left (InvalidBody "proposed call matrix exceeds shape admission")
  remaining <- checkFunctions definitions 0 definitions proposed
  if null remaining then Right () else Left (InvalidBody "proposed graph contains extra call sites")
