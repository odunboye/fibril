-- Bridge experiment only; paths are not part of Fibril's core syntax or checker.
module Fibril.Foundation.DeMorgan.ClosedCorePath

import Data.Fin
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Term
import Fibril.Core.Reduction
import Fibril.Foundation.DeMorgan.ClosedPath
import Fibril.Foundation.DeMorgan.PathSyntax
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Interval

%default total

||| Recognize the closed Boolean grammar with a shared node budget. Each
||| visited constructor consumes one unit, including branches not evaluated by
||| reduction. An unsupported node is rejected; running out first is inconclusive.
||| The returned remainder is threaded across all branches of one expression.
booleanFragment : Nat -> Term 0 -> Either PathCheck Nat
booleanFragment 0 _ = Left Exhausted
booleanFragment (S fuel) BoolTrue = Right fuel
booleanFragment (S fuel) BoolFalse = Right fuel
booleanFragment (S fuel) (BoolCase c t e) = do
  afterCondition <- booleanFragment fuel c
  afterTrue <- booleanFragment afterCondition t
  booleanFragment afterTrue e
booleanFragment (S _) _ = Left Rejected

||| Thread one admission budget through the body and both endpoint terms.
||| The caller reuses its checker-depth value as this separate node limit.
booleanInputs : Nat -> Term 0 -> Term 0 -> Term 0 -> Either PathCheck Nat
booleanInputs budget body left right = do
  afterBody <- booleanFragment budget body
  afterLeft <- booleanFragment afterBody left
  booleanFragment afterLeft right

||| Independently check all three closed core terms, then check the constant path.
||| All terms are independently checked before bounded ordinary beta conversion.
||| This remains a closed Boolean fragment, not a general cubical conversion.
public export
checkClosedCorePath : Nat -> Nat -> Nat -> Term 0 -> Term 0 -> Term 0 -> PathCheck
checkClosedCorePath depth reduction fuel body left right =
  case booleanInputs depth body left right of
    Left Rejected => Rejected
    Right _ => case checkErased depth reduction Empty body BoolType of
        Left CheckingLimit => Exhausted
        Left ReductionLimit => Exhausted
        Left _ => Rejected
        Right _ => case checkErased depth reduction Empty left BoolType of
          Left CheckingLimit => Exhausted
          Left ReductionLimit => Exhausted
          Left _ => Rejected
          Right _ => case checkErased depth reduction Empty right BoolType of
            Left CheckingLimit => Exhausted
            Left ReductionLimit => Exhausted
            Left _ => Rejected
            Right _ => case fuel of
              0 => Exhausted
              1 => Exhausted
              2 => Exhausted
              S (S (S _)) => case betaCompare reduction body left of
                Inconclusive => Exhausted
                DifferentNormalForms => Rejected
                EqualNormalForms => case betaCompare reduction body right of
                  Inconclusive => Exhausted
                  DifferentNormalForms => Rejected
                  EqualNormalForms => Accepted
    _ => Exhausted

||| Raw experimental syntax with separate dimension scope. Embedded core terms
||| are closed, so extending a dimension scope cannot capture a core variable.
||| Constructors establish scope, not typing or valid path boundaries.
public export
data CorePathExpr : Nat -> Type where
  CoreTerm : Term 0 -> CorePathExpr n
  CoreAbstract : CorePathExpr (S n) -> CorePathExpr n
  CoreApply : CorePathExpr n -> ScopedInterval n -> CorePathExpr n

||| Bound traversal of raw dimension syntax before substitution. Budgets are
||| node counts, threaded through both branches rather than duplicated.
intervalNodesWithin : Nat -> ScopedInterval n -> Maybe Nat
intervalNodesWithin 0 _ = Nothing
intervalNodesWithin (S fuel) Zero = Just fuel
intervalNodesWithin (S fuel) One = Just fuel
intervalNodesWithin (S fuel) (Var _) = Just fuel
intervalNodesWithin (S fuel) (Reverse r) = intervalNodesWithin fuel r
intervalNodesWithin (S fuel) (Meet r s) = do
  remaining <- intervalNodesWithin fuel r
  intervalNodesWithin remaining s
intervalNodesWithin (S fuel) (Join r s) = do
  remaining <- intervalNodesWithin fuel r
  intervalNodesWithin remaining s

||| Count path and interval nodes together. Core payloads are checked separately
||| by booleanFragment, since only one closed payload is admitted per body.
pathNodesWithin : Nat -> CorePathExpr n -> Maybe Nat
pathNodesWithin 0 _ = Nothing
pathNodesWithin (S fuel) (CoreTerm _) = Just fuel
pathNodesWithin (S fuel) (CoreAbstract body) = pathNodesWithin fuel body
pathNodesWithin (S fuel) (CoreApply path r) = do
  remaining <- pathNodesWithin fuel path
  intervalNodesWithin remaining r

||| Check the input path/interval node count before a caller traverses it.
||| Embedded core payloads are accounted for separately by the checker.
public export
pathWithinBudget : Nat -> CorePathExpr n -> Bool
pathWithinBudget fuel path = case pathNodesWithin fuel path of
  Just _ => True
  Nothing => False

||| Capture-avoiding substitution acts only on dimensions; embedded core
||| terms are closed and therefore remain unchanged under dimension binders.
public export
substituteCoreDimensions : (Fin n -> ScopedInterval m) -> CorePathExpr n -> CorePathExpr m
substituteCoreDimensions env (CoreTerm term) = CoreTerm term
substituteCoreDimensions env (CoreAbstract body) =
  CoreAbstract (substituteCoreDimensions (liftDimensions env) body)
substituteCoreDimensions env (CoreApply path r) =
  CoreApply (substituteCoreDimensions env path) (substituteScoped env r)

||| Substitute the newest dimension, shifting older indices down.
public export
instantiateCoreDimension : ScopedInterval n -> CorePathExpr (S n) -> CorePathExpr n
instantiateCoreDimension value = substituteCoreDimensions replace
  where
    replace : Fin (S n) -> ScopedInterval n
    replace FZ = value
    replace (FS i) = Var i

||| The body grammar consists of a closed core expression or a nested
||| application of a syntactic constant path. Its interval may be open. Each
||| nested path has the same inferred body at both endpoints; arbitrary path
||| variables, annotations, and computational captures are not admitted.
data BodyResult = BodyTerm (Term 0) | BodyRejected | BodyExhausted

collapseBody : Nat -> CorePathExpr n -> BodyResult
collapseBody 0 _ = BodyExhausted
collapseBody (S _) (CoreTerm term) = BodyTerm term
collapseBody (S fuel) (CoreApply (CoreAbstract body) r) = collapseBody fuel body
collapseBody (S _) _ = BodyRejected

||| Count the output of a dimension substitution before constructing it.
||| Each replacement is charged in full, so repeated variable occurrences
||| cannot silently bypass the output node budget.
substitutedIntervalWithin : Nat -> (Fin n -> ScopedInterval m) -> ScopedInterval n -> Maybe Nat
substitutedIntervalWithin 0 _ _ = Nothing
substitutedIntervalWithin fuel env (Var i) = intervalNodesWithin fuel (env i)
substitutedIntervalWithin (S fuel) env Zero = Just fuel
substitutedIntervalWithin (S fuel) env One = Just fuel
substitutedIntervalWithin (S fuel) env (Reverse r) = substitutedIntervalWithin fuel env r
substitutedIntervalWithin (S fuel) env (Meet r s) = do
  remaining <- substitutedIntervalWithin fuel env r
  substitutedIntervalWithin remaining env s
substitutedIntervalWithin (S fuel) env (Join r s) = do
  remaining <- substitutedIntervalWithin fuel env r
  substitutedIntervalWithin remaining env s

substitutedPathWithin : Nat -> (Fin n -> ScopedInterval m) -> CorePathExpr n -> Maybe Nat
substitutedPathWithin 0 _ _ = Nothing
substitutedPathWithin (S fuel) env (CoreTerm _) = Just fuel
substitutedPathWithin (S fuel) env (CoreAbstract body) =
  substitutedPathWithin fuel (liftDimensions env) body
substitutedPathWithin (S fuel) env (CoreApply path r) = do
  remaining <- substitutedPathWithin fuel env path
  substitutedIntervalWithin remaining env r

||| Fail before constructing a dimension-instantiated path whose path/interval
||| syntax would exceed the output node budget. Core payloads are not counted.
public export
instantiateCoreWithin : Nat -> ScopedInterval n -> CorePathExpr (S n) -> Maybe (CorePathExpr n)
instantiateCoreWithin budget value body =
  case substitutedPathWithin budget replace body of
    Nothing => Nothing
    Just _ => Just (substituteCoreDimensions replace body)
  where
    replace : Fin (S n) -> ScopedInterval n
    replace FZ = value
    replace (FS i) = Var i

||| Check a raw path expression against explicit closed core boundaries, in
||| any dimension scope. Body traversal and core/path checking each use fuel
||| as an independent depth limit. Both faces are explicitly instantiated,
||| collapsed within the supported fragment and checked against the declared
||| endpoints; unsupported forms and inconclusive checks fail closed.
public export
checkCorePathExpr : Nat -> Nat -> Nat -> CorePathExpr n -> Term 0 -> Term 0 -> PathCheck
checkCorePathExpr _ _ 0 _ _ _ = Exhausted
checkCorePathExpr depth reduction (S fuel) path@(CoreAbstract body) left right =
  case pathNodesWithin depth path of
    Nothing => Exhausted
    Just _ => case (collapseBody fuel body,
                    collapseBody fuel (instantiateCoreDimension Zero body),
                    collapseBody fuel (instantiateCoreDimension One body)) of
      (BodyRejected, _, _) => Rejected
      (_, BodyRejected, _) => Rejected
      (_, _, BodyRejected) => Rejected
      (BodyTerm term, BodyTerm face0, BodyTerm face1) =>
        case checkClosedCorePath depth reduction (S fuel) term face0 left of
          Accepted => checkClosedCorePath depth reduction (S fuel) term face1 right
          Rejected => Rejected
          Exhausted => Exhausted
      _ => Exhausted
checkCorePathExpr _ _ (S _) _ _ _ = Rejected

||| The checked beta step may preserve an open dimension scope. This result
||| is experimental raw syntax, not a core typing derivation.
public export
data CorePathStep : Nat -> Type where
  CoreStepped : CorePathExpr n -> CorePathStep n
  CoreStepRejected : CorePathStep n
  CoreStepExhausted : CorePathStep n

||| Apply a constant path at any scoped interval, including an open one. Only
||| the closed-core constant-body fragment is accepted. One fuel unit is used
||| for the application; the remaining path fuel is passed to the checker.
public export
applyCorePathAt : Nat -> Nat -> Nat -> CorePathExpr n -> ScopedInterval n -> Term 0 -> Term 0 -> CorePathStep n
applyCorePathAt _ _ 0 _ _ _ _ = CoreStepExhausted
applyCorePathAt depth reduction (S fuel) path@(CoreAbstract body) r left right =
  case intervalNodesWithin depth r of
    Nothing => CoreStepExhausted
    Just _ => case checkCorePathExpr depth reduction fuel path left right of
      Accepted => case instantiateCoreWithin depth r body of
        Just result => CoreStepped result
        Nothing => CoreStepExhausted
      Rejected => CoreStepRejected
      Exhausted => CoreStepExhausted
applyCorePathAt _ _ (S _) _ _ _ _ = CoreStepRejected

||| Result of applying the checked constant path at a literal endpoint.
public export
data CoreEndpoint = CoreValue (Term 0) | CoreRejected | CoreExhausted

||| The endpoint selector is a meta-level endpoint, not a general interval.
||| Returning the checked body is beta reduction for this constant fragment.
public export
applyClosedCoreEndpoint : Nat -> Nat -> Nat -> Bool -> Term 0 -> Term 0 -> Term 0 -> CoreEndpoint
applyClosedCoreEndpoint depth reduction fuel endpoint body left right =
  case checkClosedCorePath depth reduction fuel body left right of
    Accepted => CoreValue body
    Rejected => CoreRejected
    Exhausted => CoreExhausted

||| Instantiate an accepted body and contract its nested constant paths.
coreEndpointValue : Nat -> ScopedInterval 0 -> CorePathExpr 1 -> CoreEndpoint
coreEndpointValue fuel endpoint body = case collapseBody fuel (instantiateCoreDimension endpoint body) of
  BodyTerm term => CoreValue term
  BodyRejected => CoreRejected
  BodyExhausted => CoreExhausted

||| A closed De Morgan interval has no generators, so its value is an endpoint.
||| The depth budget is reused independently in both branches; exhaustion is
||| never treated as an endpoint. This is not a solver for open intervals.
endpointOf : Nat -> ScopedInterval 0 -> Maybe Bool
endpointOf 0 _ = Nothing
endpointOf (S _) Zero = Just False
endpointOf (S _) One = Just True
endpointOf (S _) (Var i) = absurd i
endpointOf (S fuel) (Reverse r) = map not (endpointOf fuel r)
endpointOf (S fuel) (Meet r s) = case (endpointOf fuel r, endpointOf fuel s) of
  (Just x, Just y) => Just (x && y)
  _ => Nothing
endpointOf (S fuel) (Join r s) = case (endpointOf fuel r, endpointOf fuel s) of
  (Just x, Just y) => Just (x || y)
  _ => Nothing

||| Check and reduce a raw closed application. Interval evaluation and path
||| checking each receive the remaining fuel as an independent depth limit.
public export
runCorePathExpr : Nat -> Nat -> Nat -> CorePathExpr 0 -> Term 0 -> Term 0 -> CoreEndpoint
runCorePathExpr _ _ 0 _ _ _ = CoreExhausted
runCorePathExpr depth reduction (S fuel) (CoreApply (CoreAbstract body) r) left right =
  case intervalNodesWithin depth r of
    Nothing => CoreExhausted
    Just _ => case endpointOf fuel r of
      Nothing => CoreExhausted
      Just endpoint => case checkCorePathExpr depth reduction fuel (CoreAbstract body) left right of
        Accepted => coreEndpointValue fuel (if endpoint then One else Zero) body
        Rejected => CoreRejected
        Exhausted => CoreExhausted
runCorePathExpr _ _ (S _) _ _ _ = CoreRejected
