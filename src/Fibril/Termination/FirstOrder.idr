-- Standalone first-order Nat/list prototype. Not Fibril source or core.
module Fibril.Termination.FirstOrder

import Data.List
import Fibril.Termination.SizeChange

%default total

||| The only tracked sorts. A list contains Nat values; only its tail, never its
||| head, is considered smaller than the list.
public export
data Sort = Natural | NatList

public export
Eq Sort where
  Natural == Natural = True
  NatList == NatList = True
  _ == _ = False

||| Locals are scoped indices. Unrelated values have the indicated sort and
||| contain no hidden expressions or calls in this restricted fragment.
public export
data Argument = Local Nat | Unrelated | UnrelatedList

||| Explicit calls and exhaustive control flow. CaseNat introduces its Nat
||| predecessor as local 0. CaseList introduces its tail as local 0 and Nat
||| head as local 1. LetLocal aliases a scoped value as local 0; LetOpaque
||| binds an unrelated value as local 0. Existing locals shift accordingly.
||| Neither binding contains an expression or a hidden call.
public export
data Body = End
          | Direct Nat (List Argument)
          | Both Body Body
          | Choice Body Body
          | CaseNat Nat Body Body
          | CaseList Nat Body Body
          | LetLocal Nat Body
          | LetOpaque Sort Body

||| Definition is the original Nat-only shorthand. TypedDefinition gives the
||| exact parameter sorts. No result types or quantity judgments are represented.
public export
data Function = Definition Nat Body | TypedDefinition (List Sort) Body

bodyOf : Function -> Body
bodyOf (Definition _ body) = body
bodyOf (TypedDefinition _ body) = body

parameterSorts : Function -> List Sort
parameterSorts (Definition count _) = replicate count Natural
parameterSorts (TypedDefinition sorts _) = sorts

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
admitBody (S nodes) calls (CaseList _ nil cons) = do
  (nodes, calls) <- admitBody nodes calls nil
  admitBody nodes calls cons
admitBody (S nodes) calls (LetLocal _ body) = admitBody nodes calls body
admitBody (S nodes) calls (LetOpaque _ body) = admitBody nodes calls body

admitFunctions : Nat -> Nat -> List Function -> Either Problem ()
admitFunctions nodes calls [] = Right ()
admitFunctions nodes calls (definition :: rest) = do
  case definition of
    Definition count _ => if count <= 8 then Right () else Left (AdmissionExhausted "function-argument admission exhausted (8)")
    TypedDefinition sorts _ => if within 8 sorts then Right () else Left (AdmissionExhausted "function-argument admission exhausted (8)")
  (nodes, calls) <- admitBody nodes calls (bodyOf definition)
  admitFunctions nodes calls rest

admit : List Function -> Either Problem ()
admit definitions = do
  if within 16 definitions then Right () else Left (AdmissionExhausted "function-count admission exhausted (16)")
  admitFunctions 256 128 definitions

||| Compute graph arities only after the same complete body and sort admission.
public export
admittedArities : List Function -> Either Problem (List Nat)
admittedArities definitions = do
  admit definitions
  Right (map (length . parameterSorts) definitions)

-- Producer provenance retains both sort and a row of relations to the
-- caller's original inputs. Initial rows relate only to their own argument.
record Tracked where
  constructor Track
  sort : Sort
  relations : List Relation

identityRows : List Sort -> List Tracked
identityRows sorts =
  let count = length sorts in
    zipWith (\sort, i => Track sort (map (\j => if i == j then NonIncreasing else Unknown) (indicesFrom 0 count))) sorts (indicesFrom 0 count)

strictlySmaller : Relation -> Relation
strictlySmaller Unknown = Unknown
strictlySmaller NonIncreasing = Decreases
strictlySmaller Decreases = Decreases

argumentRow : Nat -> List Tracked -> Sort -> Argument -> Either Problem (List Relation)
argumentRow width env expected (Local index) = case at index env of
  Just value => if value.sort == expected then Right value.relations else Left (InvalidBody "call argument sort does not match its target")
  Nothing => Left (InvalidBody "call argument references an out-of-scope local")
argumentRow width env Natural Unrelated = Right (replicate width Unknown)
argumentRow width env NatList UnrelatedList = Right (replicate width Unknown)
argumentRow _ _ _ _ = Left (InvalidBody "call argument sort does not match its target")

argumentRows : Nat -> List Tracked -> List Sort -> List Argument -> Either Problem (List (List Relation))
argumentRows width env [] [] = Right []
argumentRows width env (expected :: sorts) (arg :: args) = do
  row <- argumentRow width env expected arg
  following <- argumentRows width env sorts args
  Right (row :: following)
argumentRows _ _ _ _ = Left (InvalidBody "call arity does not match its target")

extractBody : List Function -> Nat -> Nat -> List Tracked -> Body -> List Call -> Either Problem (List Call)
extractBody definitions caller width env End edges = Right edges
extractBody definitions caller width env (Direct target args) edges = do
  callee <- case at target definitions of
    Nothing => Left (InvalidBody "call target is outside the function group")
    Just definition => Right definition
  rows <- argumentRows width env (parameterSorts callee) args
  Right (Edge caller target rows :: edges)
extractBody definitions caller width env (Both left right) edges = do
  edges <- extractBody definitions caller width env left edges
  extractBody definitions caller width env right edges
extractBody definitions caller width env (Choice left right) edges = do
  edges <- extractBody definitions caller width env left edges
  extractBody definitions caller width env right edges
extractBody definitions caller width env (CaseNat local zero successor) edges = do
  value <- case at local env of
    Nothing => Left (InvalidBody "Nat case references an out-of-scope local")
    Just value => if value.sort == Natural then Right value else Left (InvalidBody "Nat case scrutinee has the wrong sort")
  if within 15 env then Right () else Left (AdmissionExhausted "local-scope admission exhausted (16)")
  edges <- extractBody definitions caller width env zero edges
  extractBody definitions caller width (Track Natural (map strictlySmaller value.relations) :: env) successor edges
extractBody definitions caller width env (CaseList local nil cons) edges = do
  value <- case at local env of
    Nothing => Left (InvalidBody "list case references an out-of-scope local")
    Just value => if value.sort == NatList then Right value else Left (InvalidBody "list case scrutinee has the wrong sort")
  if within 14 env then Right () else Left (AdmissionExhausted "local-scope admission exhausted (16)")
  edges <- extractBody definitions caller width env nil edges
  let tail = Track NatList (map strictlySmaller value.relations)
  let head = Track Natural (replicate width Unknown)
  extractBody definitions caller width (tail :: head :: env) cons edges
extractBody definitions caller width env (LetLocal local body) edges = do
  value <- case at local env of
    Nothing => Left (InvalidBody "local alias references an out-of-scope local")
    Just value => Right value
  if within 15 env then Right () else Left (AdmissionExhausted "local-scope admission exhausted (16)")
  extractBody definitions caller width (value :: env) body edges
extractBody definitions caller width env (LetOpaque sort body) edges = do
  if within 15 env then Right () else Left (AdmissionExhausted "local-scope admission exhausted (16)")
  extractBody definitions caller width (Track sort (replicate width Unknown) :: env) body edges

extractFunctions : List Function -> Nat -> List Function -> List Call -> Either Problem (List Call)
extractFunctions definitions caller [] edges = Right (reverse edges)
extractFunctions definitions caller (definition :: rest) edges = do
  let sorts = parameterSorts definition
  edges <- extractBody definitions caller (length sorts) (identityRows sorts) (bodyOf definition) edges
  extractFunctions definitions (S caller) rest edges

||| Extract all direct call-site matrices from this synthetic Nat/list body.
||| Success is about this fragment only; it certifies no Fibril program.
public export
extract : List Function -> Either Problem (List Call)
extract definitions = do
  admit definitions
  extractFunctions definitions 0 definitions []

-- The independent body walk uses root/descendant provenance rather than the
-- producer's relation rows. A list head has no known originating argument.
data Origin = Root Sort Nat | Descendant Sort Nat | NoOrigin Sort

originSort : Origin -> Sort
originSort (Root sort _) = sort
originSort (Descendant sort _) = sort
originSort (NoOrigin sort) = sort

descendant : Origin -> Origin
descendant (Root sort index) = Descendant sort index
descendant (Descendant sort index) = Descendant sort index
descendant (NoOrigin sort) = NoOrigin sort

originRelation : Origin -> Nat -> Relation
originRelation (Root _ index) column = if index == column then NonIncreasing else Unknown
originRelation (Descendant _ index) column = if index == column then Decreases else Unknown
originRelation (NoOrigin _) _ = Unknown

rowMatches : Nat -> List Origin -> Sort -> Argument -> List Relation -> Bool
rowMatches width env expected (Local index) row = case at index env of
  Nothing => False
  Just origin => originSort origin == expected && row == map (originRelation origin) (indicesFrom 0 width)
rowMatches width env Natural Unrelated row = row == replicate width Unknown
rowMatches width env NatList UnrelatedList row = row == replicate width Unknown
rowMatches _ _ _ _ _ = False

rowsMatch : Nat -> List Origin -> List Sort -> List Argument -> List (List Relation) -> Bool
rowsMatch width env [] [] [] = True
rowsMatch width env (sort :: sorts) (argument :: args) (row :: rows) =
  rowMatches width env sort argument row && rowsMatch width env sorts args rows
rowsMatch _ _ _ _ _ = False

checkBody : List Function -> Nat -> Nat -> List Origin -> Body -> List Call -> Either Problem (List Call)
checkBody definitions caller width env End edges = Right edges
checkBody definitions caller width env (Direct target args) [] = Left (InvalidBody "proposed graph omits a call site")
checkBody definitions caller width env (Direct target args) (edge :: edges) = do
  callee <- case at target definitions of
    Nothing => Left (InvalidBody "call target is outside the function group")
    Just definition => Right definition
  if edge.caller == caller && edge.callee == target &&
     rowsMatch width env (parameterSorts callee) args edge.matrix
    then Right edges else Left (InvalidBody "proposed call edge does not match the body, target sorts or arity")
checkBody definitions caller width env (Both left right) edges = do
  edges <- checkBody definitions caller width env left edges
  checkBody definitions caller width env right edges
checkBody definitions caller width env (Choice left right) edges = do
  edges <- checkBody definitions caller width env left edges
  checkBody definitions caller width env right edges
checkBody definitions caller width env (CaseNat local zero successor) edges = do
  origin <- case at local env of
    Nothing => Left (InvalidBody "Nat case references an out-of-scope local")
    Just origin => if originSort origin == Natural then Right origin else Left (InvalidBody "Nat case scrutinee has the wrong sort")
  if within 15 env then Right () else Left (AdmissionExhausted "local-scope admission exhausted (16)")
  edges <- checkBody definitions caller width env zero edges
  checkBody definitions caller width (descendant origin :: env) successor edges
checkBody definitions caller width env (CaseList local nil cons) edges = do
  origin <- case at local env of
    Nothing => Left (InvalidBody "list case references an out-of-scope local")
    Just origin => if originSort origin == NatList then Right origin else Left (InvalidBody "list case scrutinee has the wrong sort")
  if within 14 env then Right () else Left (AdmissionExhausted "local-scope admission exhausted (16)")
  edges <- checkBody definitions caller width env nil edges
  checkBody definitions caller width (descendant origin :: NoOrigin Natural :: env) cons edges
checkBody definitions caller width env (LetLocal local body) edges = do
  origin <- case at local env of
    Nothing => Left (InvalidBody "local alias references an out-of-scope local")
    Just origin => Right origin
  if within 15 env then Right () else Left (AdmissionExhausted "local-scope admission exhausted (16)")
  checkBody definitions caller width (origin :: env) body edges
checkBody definitions caller width env (LetOpaque sort body) edges = do
  if within 15 env then Right () else Left (AdmissionExhausted "local-scope admission exhausted (16)")
  checkBody definitions caller width (NoOrigin sort :: env) body edges

checkFunctions : List Function -> Nat -> List Function -> List Call -> Either Problem (List Call)
checkFunctions definitions caller [] edges = Right edges
checkFunctions definitions caller (definition :: rest) edges = do
  let sorts = parameterSorts definition
  let env = zipWith Root sorts (indicesFrom 0 (length sorts))
  edges <- checkBody definitions caller (length sorts) env (bodyOf definition) edges
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

||| Bind the graph and closure checks to the exact same synthetic bodies. A
||| Right verdict is still only about this fragment, not a Fibril program.
||| InvalidBody and AdmissionExhausted remain distinct from graph verdicts.
public export
verifyBody : List Function -> List Call -> List Call -> Either Problem Verdict
verifyBody definitions proposed certificate = do
  check definitions proposed
  sizes <- admittedArities definitions
  Right (verify sizes proposed certificate)
