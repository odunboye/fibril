-- A fixed, non-dependent telescope: A-variables followed by path declarations.
module Fibril.Cubical.Logical.PathContext

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.OpenPath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Restriction

%default total

public export
PathContext : Nat -> Nat -> Type
PathContext m k = Vect k (NeutralPath m)

public export
data ContextTerm : Nat -> Nat -> Nat -> Type where
  Variable : Fin m -> ContextTerm m k n
  ApplyPath : Fin k -> ScopedInterval n -> ContextTerm m k n

public export
mapContextDimensions : (Fin n -> ScopedInterval d) -> ContextTerm m k n -> ContextTerm m k d
mapContextDimensions env (Variable x) = Variable x
mapContextDimensions env (ApplyPath p r) = ApplyPath p (substituteScoped env r)

public export
renameContextTerms : (Fin m -> Fin a) -> ContextTerm m k n -> ContextTerm a k n
renameContextTerms env (Variable x) = Variable (env x)
renameContextTerms env (ApplyPath p r) = ApplyPath p r

public export
renameContext : (Fin m -> Fin a) -> PathContext m k -> PathContext a k
renameContext env = map (renamePath env)

-- Bound dimensions and both context lengths as well as syntax before any
-- solver call or Fin comparison; the admission allowance is not solver fuel.
admit : {m, k, n : Nat} -> Nat -> ScopedFace n -> ContextTerm m k n -> ContextTerm m k n -> Bool
admit {m} {k} {n} budget face a b =
  m <= 12 && k <= 12 && n <= 12 && isJust (faceNodes (min 12 budget) face >>= \f => termNodes f a >>= \g => termNodes g b)
  where
    termNodes : Nat -> ContextTerm m k n -> Maybe Nat
    termNodes Z _ = Nothing
    termNodes (S f) (Variable _) = Just f
    termNodes (S f) (ApplyPath _ r) = intervalNodes f r

endpointMatch : NeutralPath m -> ScopedInterval n -> NeutralPath m -> ScopedInterval n -> ScopedFace n
endpointMatch p r q s =
  SDisjunction
    (SDisjunction (pair (left p == left q) False False) (pair (left p == right q) False True))
    (SDisjunction (pair (right p == left q) True False) (pair (right p == right q) True True))
  where
    pair : Bool -> Bool -> Bool -> ScopedFace n
    pair False _ _ = SBottom
    pair True x y = SConjunction (scopedEndpoint r x) (scopedEndpoint s y)

||| Sufficient conversion; distinct path names only compare at common endpoints.
public export
convert : {m, k, n : Nat} -> Nat -> Restriction n -> PathContext m k -> ContextTerm m k n -> ContextTerm m k n -> Result
convert budget (Under face) ctx a b =
  if not (admit budget face a b) then Exhausted else
  case (a, b) of
    (Variable x, Variable y) => if x == y || holds (Under face) SBottom then Accepted else Rejected
    (Variable x, ApplyPath p r) => convertToVariable budget (Under face) (index p ctx) (At r) x
    (ApplyPath p r, Variable x) => convertToVariable budget (Under face) (index p ctx) (At r) x
    (ApplyPath p r, ApplyPath q s) =>
      if p == q then convertNeutrals budget (Under face) (index p ctx) r s
      else if holds (Under face) (endpointMatch (index p ctx) r (index q ctx) s) then Accepted else Rejected

||| Check a dimension abstraction against its declared variable endpoints.
public export
checkContextAbstraction : {m, k, n : Nat} -> Nat -> PathContext m k -> ContextTerm m k (S n) -> Fin m -> Fin m -> Result
checkContextAbstraction budget ctx body l r =
  -- Admit the original body before substitution, so substitution cannot hide size.
  if not (admit budget STop body (Variable l)) then Exhausted else
  case convert budget unrestricted ctx (mapContextDimensions zero body) (Variable l) of
    Accepted => convert budget unrestricted ctx (mapContextDimensions one body) (Variable r)
    other => other
  where
    zero : Fin (S n) -> ScopedInterval n
    zero FZ = Zero
    zero (FS i) = Var i
    one : Fin (S n) -> ScopedInterval n
    one FZ = One
    one (FS i) = Var i

||| Evidence ties the exact context, body and endpoints to a successful check.
||| This is experimental logical evidence, not a runtime path.
export
data CheckedContextAbstraction : (ctx : PathContext m k) ->
                                 (body : ContextTerm m k (S n)) ->
                                 (l : Fin m) -> (r : Fin m) -> Type where
  MkCheckedContextAbstraction : CheckedContextAbstraction ctx body l r

||| Only the checker can create evidence; Accepted alone is not evidence.
export
checkBoundAbstraction : {m, k, n : Nat} -> (budget : Nat) -> (ctx : PathContext m k) ->
                        (body : ContextTerm m k (S n)) -> (l : Fin m) -> (r : Fin m) ->
                        Either Result (CheckedContextAbstraction ctx body l r)
checkBoundAbstraction budget ctx body l r =
  case checkContextAbstraction budget ctx body l r of
    Accepted => Right MkCheckedContextAbstraction
    other => Left other

||| Lift a simultaneous substitution beneath the abstraction's newest dimension.
public export
liftContextDimensions : (Fin n -> ScopedInterval d) -> Fin (S n) -> ScopedInterval (S d)
liftContextDimensions env FZ = Var FZ
liftContextDimensions env (FS i) = weakenInterval (env i)

||| Recheck both source and transformed abstractions under the supplied allowance.
||| The transformed syntax is admitted by the checker before any solver call.
export
substituteBoundDimensions : {m, k, n, d : Nat} -> (budget : Nat) -> (env : Fin n -> ScopedInterval d) ->
                            {ctx : PathContext m k} -> {body : ContextTerm m k (S n)} ->
                            {l, r : Fin m} -> CheckedContextAbstraction ctx body l r ->
                            Either Result (CheckedContextAbstraction ctx
                              (mapContextDimensions (liftContextDimensions env) body) l r)
substituteBoundDimensions budget env {ctx} {body} {l} {r} MkCheckedContextAbstraction =
  case checkContextAbstraction budget ctx body l r of
    Accepted => checkBoundAbstraction budget ctx (mapContextDimensions (liftContextDimensions env) body) l r
    other => Left other

-- Admission and output accounting share one allowance. Counts are bounded
-- before indexing the vector or traversing any Fin carried by the syntax.
environmentNodes : Nat -> Vect n (ScopedInterval d) -> Maybe Nat
environmentNodes fuel [] = Just fuel
environmentNodes Z (_ :: _) = Nothing
environmentNodes (S fuel) (x :: xs) = do
  rest <- intervalNodes fuel x
  environmentNodes rest xs

substitutedIntervalNodes : Nat -> Vect n (ScopedInterval d) -> ScopedInterval (S n) -> Maybe Nat
substitutedIntervalNodes Z _ _ = Nothing
substitutedIntervalNodes (S fuel) env Zero = Just fuel
substitutedIntervalNodes (S fuel) env One = Just fuel
substitutedIntervalNodes (S fuel) env (Var FZ) = Just fuel
substitutedIntervalNodes fuel env (Var (FS i)) = intervalNodes fuel (index i env)
substitutedIntervalNodes (S fuel) env (Reverse x) = substitutedIntervalNodes fuel env x
substitutedIntervalNodes (S fuel) env (Meet x y) = do
  rest <- substitutedIntervalNodes fuel env x
  substitutedIntervalNodes rest env y
substitutedIntervalNodes (S fuel) env (Join x y) = do
  rest <- substitutedIntervalNodes fuel env x
  substitutedIntervalNodes rest env y

||| Preflight counts every environment entry and every output occurrence,
||| including unused entries and duplicated replacements. Context lengths and
||| dimension counts are capped independently of the supplied allowance.
||| The output term cap is 10: the checker also admits STop and Variable.
public export
boundedSubstitutionPreflight : {m, k, n, d : Nat} -> Nat -> Vect n (ScopedInterval d) -> ContextTerm m k (S n) -> Bool
boundedSubstitutionPreflight {m} {k} {n} {d} budget env body =
  if not (m <= 12 && k <= 12 && n <= 11 && d <= 11) then False else
  isJust (environmentNodes budget env >>= \rest => outputNodes (min 10 rest) body)
  where
    outputNodes : Nat -> ContextTerm m k (S n) -> Maybe Nat
    outputNodes Z _ = Nothing
    outputNodes (S f) (Variable _) = Just f
    outputNodes (S f) (ApplyPath _ r) = substitutedIntervalNodes f env r

||| Finite first-order substitution for untrusted syntax. The original check
||| precedes admission; output syntax is constructed only after preflight.
export
substituteBoundDimensionsFinite : {m, k, n, d : Nat} -> (budget : Nat) -> (env : Vect n (ScopedInterval d)) ->
                            {ctx : PathContext m k} -> {body : ContextTerm m k (S n)} ->
                            {l, r : Fin m} -> CheckedContextAbstraction ctx body l r ->
                            Either Result (CheckedContextAbstraction ctx
                              (mapContextDimensions (liftContextDimensions (\i => index i env)) body) l r)
substituteBoundDimensionsFinite budget env {ctx} {body} {l} {r} MkCheckedContextAbstraction =
  case checkContextAbstraction budget ctx body l r of
    Accepted => if boundedSubstitutionPreflight budget env body
      then checkBoundAbstraction budget ctx (mapContextDimensions (liftContextDimensions (\i => index i env)) body) l r
      else Left Exhausted
    other => Left other
