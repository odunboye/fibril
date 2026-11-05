-- Bounded first-order inference of erased constructor-prefix arguments.
-- Metavariables live only in this elaborator's scope map, never in core terms.
module Fibril.Elaboration.Expression.Parameters

import Data.Fin
import Data.List
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Limits
import Fibril.Source.Text
import Fibril.Source.Resolve.Error
import Fibril.Elaboration.Expression.Scope
import Fibril.Elaboration.Expression.Conversion
import Fibril.Elaboration.Expression.Payload

%default total

public export
inferredParameterNodes : Nat
inferredParameterNodes = 512

ScopeMap : Nat -> Nat -> Type
ScopeMap from into = Fin from -> Maybe (Either Nat (Fin into))

Solutions : Nat -> Type
Solutions base = List (Nat, Term base)

failure : Position -> Either ResolveError a
failure position = Left (CannotElaborate position
  "Cannot infer erased constructor parameters from the scrutinee type; supply them explicitly")

liftMap : ScopeMap m a -> ScopeMap (S m) (S a)
liftMap mapping FZ = Just (Right FZ)
liftMap mapping (FS i) = case mapping i of
  Nothing => Nothing
  Just (Left meta) => Just (Left meta)
  Just (Right outer) => Just (Right (FS outer))

liftPrune : (Fin a -> Maybe (Fin base)) -> Fin (S a) -> Maybe (Fin base)
liftPrune prune FZ = Nothing
liftPrune prune (FS i) = prune i

bindMeta : Position -> Nat -> Term base -> Solutions base -> Either ResolveError (Solutions base)
bindMeta position meta value solutions = case lookup meta solutions of
  Nothing => Right ((meta, value) :: solutions)
  Just previous => if guardedEqual typeReductionFuel previous value
    then Right solutions
    else Left (CannotElaborate position "Parameter consistency comparison failed or was inconclusive; supply parameters explicitly")

mutual
  match : Position -> ScopeMap m a -> (Fin a -> Maybe (Fin base)) ->
          Term m -> Term a -> Solutions base -> Either ResolveError (Solutions base)
  match position mapping prune (Variable i) value solutions = case mapping i of
    Just (Left meta) => case thin prune value of
      Nothing => failure position
      Just value => bindMeta position meta value solutions
    Just (Right expected) => case value of
      Variable actual => if expected == actual then Right solutions else failure position
      _ => failure position
    Nothing => failure position
  match position mapping prune (Universe x) (Universe y) solutions =
    if x == y then Right solutions else failure position
  match position mapping prune UnitType UnitType solutions = Right solutions
  match position mapping prune UnitValue UnitValue solutions = Right solutions
  match position mapping prune BoolType BoolType solutions = Right solutions
  match position mapping prune BoolTrue BoolTrue solutions = Right solutions
  match position mapping prune BoolFalse BoolFalse solutions = Right solutions
  match position mapping prune ReadLine ReadLine solutions = Right solutions
  match position mapping prune (FileHandleValue left first) (FileHandleValue right second) solutions =
    if left == right && first == second then Right solutions else failure position
  match position mapping prune (ReadInputFile left) (ReadInputFile right) solutions = match position mapping prune left right solutions
  match position mapping prune StringType StringType solutions = Right solutions
  match position mapping prune (StringValue x) (StringValue y) solutions =
    if x == y then Right solutions else failure position
  match position mapping prune (BoxType q x) (BoxType r y) solutions =
    if q == r then match position mapping prune x y solutions else failure position
  match position mapping prune (NominalType key xs shape) (NominalType other ys actualShape) solutions =
    if key == other then do
      solutions <- matchTerms position mapping prune xs ys solutions
      match position mapping prune shape actualShape solutions
    else failure position
  match position mapping prune (VariantType xs) (VariantType ys) solutions = matchArms position mapping prune xs ys solutions
  match position mapping prune (WithInputFile a p f) (WithInputFile b q g) solutions = do
    first <- match position mapping prune a b solutions
    second <- match position mapping prune p q first
    match position mapping prune f g second
  match position mapping prune (IOType x) (IOType y) solutions = match position mapping prune x y solutions
  match position mapping prune (FileHandleType x) (FileHandleType y) solutions = match position mapping prune x y solutions
  match position mapping prune (IOPure x) (IOPure y) solutions = match position mapping prune x y solutions
  match position mapping prune (WriteLine x) (WriteLine y) solutions = match position mapping prune x y solutions
  match position mapping prune (BoxValue x y) (BoxValue u v) solutions = pair position mapping prune x y u v solutions
  match position mapping prune (Apply x y) (Apply u v) solutions = pair position mapping prune x y u v solutions
  match position mapping prune (StringAppend x y) (StringAppend u v) solutions = pair position mapping prune x y u v solutions
  match position mapping prune (StringEqual x y) (StringEqual u v) solutions = pair position mapping prune x y u v solutions
  match position mapping prune (UnitCase x y) (UnitCase u v) solutions = pair position mapping prune x y u v solutions
  match position mapping prune (BoolCase x y z) (BoolCase u v w) solutions = triple position mapping prune x y z u v w solutions
  match position mapping prune (BoxCase x y z) (BoxCase u v w) solutions = triple position mapping prune x y z u v w solutions
  match position mapping prune (PairValue x y z) (PairValue u v w) solutions = triple position mapping prune x y z u v w solutions
  match position mapping prune (PairCase x y z) (PairCase u v w) solutions = triple position mapping prune x y z u v w solutions
  match position mapping prune (IOBind x y z w) (IOBind u v a b) solutions = do
    solutions <- triple position mapping prune x y z u v a solutions
    match position mapping prune w b solutions
  match position mapping prune (Pi q x y) (Pi r u v) solutions =
    if q == r then binder position mapping prune x y u v solutions else failure position
  match position mapping prune (Lambda q x y) (Lambda r u v) solutions =
    if q == r then binder position mapping prune x y u v solutions else failure position
  match position mapping prune (Sigma q r x y) (Sigma s t u v) solutions =
    if q == s && r == t then binder position mapping prune x y u v solutions else failure position
  match position mapping prune _ _ solutions = failure position

  matchTerms : Position -> ScopeMap m a -> (Fin a -> Maybe (Fin base)) -> List (Term m) -> List (Term a) -> Solutions base -> Either ResolveError (Solutions base)
  matchTerms position mapping prune [] [] solutions = Right solutions
  matchTerms position mapping prune (x :: xs) (y :: ys) solutions = do
    solutions <- match position mapping prune x y solutions
    matchTerms position mapping prune xs ys solutions
  matchTerms position mapping prune _ _ solutions = failure position

  matchArms : Position -> ScopeMap m a -> (Fin a -> Maybe (Fin base)) -> List (Maybe (Quantity, Term m)) -> List (Maybe (Quantity, Term a)) -> Solutions base -> Either ResolveError (Solutions base)
  matchArms position mapping prune [] [] solutions = Right solutions
  matchArms position mapping prune (Nothing :: xs) (Nothing :: ys) solutions = matchArms position mapping prune xs ys solutions
  matchArms position mapping prune (Just (q, x) :: xs) (Just (r, y) :: ys) solutions =
    if q == r then do
      solutions <- match position mapping prune x y solutions
      matchArms position mapping prune xs ys solutions
    else failure position
  matchArms position mapping prune _ _ solutions = failure position

  pair : Position -> ScopeMap m a -> (Fin a -> Maybe (Fin base)) ->
         Term m -> Term m -> Term a -> Term a -> Solutions base -> Either ResolveError (Solutions base)
  pair position mapping prune x y u v solutions = do
    solutions <- match position mapping prune x u solutions
    match position mapping prune y v solutions

  triple : Position -> ScopeMap m a -> (Fin a -> Maybe (Fin base)) ->
           Term m -> Term m -> Term m -> Term a -> Term a -> Term a ->
           Solutions base -> Either ResolveError (Solutions base)
  triple position mapping prune x y z u v w solutions = do
    solutions <- pair position mapping prune x y u v solutions
    match position mapping prune z w solutions

  binder : Position -> ScopeMap m a -> (Fin a -> Maybe (Fin base)) ->
           Term m -> Term (S m) -> Term a -> Term (S a) ->
           Solutions base -> Either ResolveError (Solutions base)
  binder position mapping prune x y u v solutions = do
    solutions <- match position mapping prune x u solutions
    match position (liftMap mapping) (liftPrune prune) y v solutions

expose : Position -> Term n -> Either ResolveError (Term n)
expose position ty = case weakHead typeReductionFuel ty of
  HeadForm result => Right result
  HeadLimit _ => Left (CannotElaborate position "Constructor parameter inference exhausted its reduction budget")

piCount : Position -> Nat -> Term n -> Either ResolveError Nat
piCount position Z ty = Left (CannotElaborate position "Constructor parameter telescope depth exhausted")
piCount position (S fuel) ty = do
  ty <- expose position ty
  case ty of
    Pi _ _ body => S <$> piCount position fuel body
    _ => Right 0

data Problem : Nat -> Type where
  Prepared : Term m -> ScopeMap m base -> Problem base

openFields : Position -> Nat -> Term m -> ScopeMap m base -> Either ResolveError (Problem base)
openFields position Z ty mapping = Right (Prepared ty mapping)
openFields position (S fields) ty mapping = do
  ty <- expose position ty
  case ty of
    Pi _ _ rest =>
      let next : ScopeMap (S m) base
          next FZ = Nothing
          next (FS i) = mapping i
       in openFields position fields rest next
    _ => failure position

openParameters : Position -> Nat -> Nat -> Nat -> Term m -> ScopeMap m base ->
                 Either ResolveError (Problem base)
openParameters position Z fields index ty mapping = openFields position fields ty mapping
openParameters position (S params) fields index ty mapping = do
  ty <- expose position ty
  case ty of
    Pi Erased _ rest =>
      let next : ScopeMap (S m) base
          next FZ = Just (Left index)
          next (FS i) = mapping i
       in openParameters position params fields (S index) rest next
    _ => failure position

normalType : Position -> Term n -> Either ResolveError (Term n)
normalType position ty = do
  if typeNodes ty > inferredParameterNodes
     then Left (CannotElaborate position "Constructor parameter inference types exceed 512 nodes; supply parameters explicitly") else Right ()
  normal <- case normalize typeReductionFuel ty of
    Normal result => Right result
    OutOfFuel _ => Left (CannotElaborate position "Constructor parameter inference exhausted its reduction budget")
  if typeNodes normal > inferredParameterNodes
     then Left (CannotElaborate position "Constructor parameter inference types exceed 512 nodes; supply parameters explicitly")
     else Right normal

arguments : Position -> Nat -> Nat -> Solutions base -> Either ResolveError (List (Term base))
arguments position Z index solutions = Right []
arguments position (S count) index solutions = do
  value <- case lookup index solutions of Nothing => failure position; Just value => Right value
  rest <- arguments position count (S index) solutions
  Right (value :: rest)

||| Solver-specific limits are admissions, not hard time or memory guarantees.
public export
implicitTelescopeLimit : Nat
implicitTelescopeLimit = 64

public export
implicitProposalDepth : Nat
implicitProposalDepth = 16

implicitConstraintBudget : Nat
implicitConstraintBudget = 262144

constraintCost : Term m -> Term n -> Nat
constraintCost pattern actual =
  (1 + typeNodes pattern + payloadSize pattern) * (1 + typeNodes actual + payloadSize actual)

implicitFailure : Position -> Either ResolveError a
implicitFailure position = Left (CannotElaborate position "Cannot infer implicit arguments; use explicit {arguments}")

openImplicitRaw : Position -> Nat -> Nat -> Term m -> ScopeMap m base -> Either ResolveError (Problem base)
openImplicitRaw position Z index ty mapping = Right (Prepared ty mapping)
openImplicitRaw position (S remaining) index (Pi Erased _ rest) mapping =
  let next : ScopeMap (S m) base
      next FZ = Just (Left index)
      next (FS i) = mapping i in
    openImplicitRaw position remaining (S index) rest next
openImplicitRaw position _ _ _ _ = implicitFailure position

skipExplicit : ScopeMap m base -> ScopeMap (S m) base
skipExplicit mapping FZ = Nothing
skipExplicit mapping (FS i) = mapping i

seedImplicit : Nat -> List (Term n) -> Solutions n
seedImplicit index [] = []
seedImplicit index (value :: rest) = (index, value) :: seedImplicit (S index) rest

-- Propose argument types without normalizing caller-authored terms. The final
-- independent checker validates both the argument and the proposed type.
lookupImplicitType : Position -> Nat -> (Fin m -> Fin n) -> Context m -> Fin m -> Either ResolveError (Term n)
lookupImplicitType position Z env context index =
  Left (CannotElaborate position "Implicit local context admission exhausted (64); use explicit {arguments}")
lookupImplicitType position (S fuel) env (Extend rest quantity domain) FZ = do
  if typeNodes domain > inferredParameterNodes || payloadSize domain > payloadLimit
    then Left (CannotElaborate position "Implicit local type exceeds node or payload admission") else Right ()
  Right (rename (\i => env (FS i)) domain)
lookupImplicitType position (S fuel) env (Extend rest quantity domain) (FS i) =
  lookupImplicitType position fuel (\j => env (FS j)) rest i

public export
implicitArgumentType : Position -> Nat -> Context n -> Term n -> Either ResolveError (Maybe (Term n))
implicitArgumentType position Z context _ = Left (CannotElaborate position "Implicit argument type proposal depth exhausted; use explicit {arguments}")
implicitArgumentType position (S fuel) context (Variable index) = Just <$> lookupImplicitType position implicitTelescopeLimit id context index
implicitArgumentType position (S fuel) context (StringValue _) = Right (Just StringType)
implicitArgumentType position (S fuel) context BoolTrue = Right (Just BoolType)
implicitArgumentType position (S fuel) context BoolFalse = Right (Just BoolType)
implicitArgumentType position (S fuel) context ReadLine = Right (Just (IOType readResultType))
implicitArgumentType position (S fuel) context (FileHandleValue identity _) = Right (Just (FileHandleType (runtimeFileRegion identity)))
implicitArgumentType position (S fuel) context UnitValue = Right (Just UnitType)
implicitArgumentType position (S fuel) context StringType = Right (Just (Universe 0))
implicitArgumentType position (S fuel) context BoolType = Right (Just (Universe 0))
implicitArgumentType position (S fuel) context UnitType = Right (Just (Universe 0))
implicitArgumentType position (S fuel) context (Universe level) = Right (Just (Universe (S level)))
implicitArgumentType position (S fuel) context (StringAppend _ _) = Right (Just StringType)
implicitArgumentType position (S fuel) context (StringEqual _ _) = Right (Just BoolType)
implicitArgumentType position (S fuel) context (NominalValue ty _) = Right (Just ty)
implicitArgumentType position (S fuel) context (VariantValue ty _ _) = Right (Just ty)
implicitArgumentType position (S fuel) context (BoxValue ty _) = Right (Just ty)
implicitArgumentType position (S fuel) context (PairValue ty _ _) = Right (Just ty)
implicitArgumentType position (S fuel) context (UnitCase _ body) = implicitArgumentType position fuel context body
implicitArgumentType position (S fuel) context (BoolCase _ yes _) = implicitArgumentType position fuel context yes
-- This proposes an annotation only; the original application remains checked.
implicitArgumentType position (S fuel) context (Apply (Lambda _ domain (Variable FZ)) _) = Right (Just domain)
implicitArgumentType position (S fuel) context (Pi q domain body) = do
  if typeNodes domain > inferredParameterNodes || payloadSize domain > payloadLimit
    then Left (CannotElaborate position "Implicit Pi domain exceeds admission") else Right ()
  domainType <- implicitArgumentType position fuel context domain
  bodyType <- implicitArgumentType position fuel (Extend context q domain) body
  case (domainType, bodyType) of
    (Just (Universe left), Just (Universe right)) => Right (Just (Universe (max left right)))
    _ => Right Nothing
implicitArgumentType position (S fuel) context (Lambda q domain body) = do
  if typeNodes domain > inferredParameterNodes || payloadSize domain > payloadLimit
    then Left (CannotElaborate position "Implicit lambda domain exceeds admission") else Right ()
  result <- implicitArgumentType position fuel (Extend context q domain) body
  case result of
    Nothing => Right Nothing
    Just ty => do
      if 1 + typeNodes domain + typeNodes ty > inferredParameterNodes ||
         payloadSize domain + payloadSize ty > payloadLimit
        then Left (CannotElaborate position "Implicit lambda type exceeds admission") else Right ()
      Right (Just (Pi q domain ty))
implicitArgumentType position (S fuel) context (Apply function argument) = do
  proposed <- implicitArgumentType position fuel context function
  case proposed of
    Nothing => Right Nothing
    Just ty => do
      if typeNodes ty > inferredParameterNodes || payloadSize ty > payloadLimit ||
         typeNodes argument > inferredParameterNodes || payloadSize argument > payloadLimit
        then Left (CannotElaborate position "Implicit application type proposal exceeds admission") else Right ()
      case ty of
        Pi _ _ result => do
          let nodes : Fin (S n) -> Nat
              nodes FZ = typeNodes argument
              nodes (FS _) = 1
          let payloads : Fin (S n) -> Nat
              payloads FZ = payloadSize argument
              payloads (FS _) = 0
          if substitutionNodes nodes result > inferredParameterNodes || payloadWeight payloads result > payloadLimit
            then Left (CannotElaborate position "Implicit application substitution exceeds admission") else Right ()
          Right (Just (instantiateTerm argument result))
        _ => Right Nothing
implicitArgumentType position (S fuel) context _ = Right Nothing


checkImplicitDomains : Position -> Context n -> Term n -> List (Term n) -> Either ResolveError ()
checkImplicitDomains position context ty [] = Right ()
checkImplicitDomains position context (Pi Erased domain rest) (solution :: remaining) = do
  -- Domains and solutions are validated by the independent whole-term checker.
  -- This step only checks substitution admission before constructing a type.
  case remaining of
    [] => Right ()
    _ => do
      let weights : Fin (S n) -> Nat
          weights FZ = typeNodes solution
          weights (FS _) = 1
      let payloadWeights : Fin (S n) -> Nat
          payloadWeights FZ = payloadSize solution
          payloadWeights (FS _) = 0
      if substitutionNodes weights rest > inferredParameterNodes || payloadWeight payloadWeights rest > payloadLimit
        then Left (CannotElaborate position "Implicit telescope substitution exceeds node or payload admission; use explicit {arguments}") else Right ()
      checkImplicitDomains position context (instantiateTerm solution rest) remaining
checkImplicitDomains position context _ _ = implicitFailure position

||| Scoped, untrusted application constraints; never a checked certificate.
public export
record ImplicitState (n : Nat) where
  constructor ImplicitConstraints
  count : Nat
  signature : Term n
  problem : Problem n
  solutions : Solutions n
  remainingWork : Nat
  steps : Nat

public export
beginImplicit : Position -> Nat -> Term n -> List (Term n) -> Either ResolveError (ImplicitState n)
beginImplicit position count ty given = do
  if count > implicitTelescopeLimit
    then Left (CannotElaborate position "Implicit inference telescope admission exhausted (64)") else Right ()
  if length given > count then Left (CannotElaborate position "Too many explicit {arguments}") else Right ()
  if typeNodes ty > inferredParameterNodes || payloadSize ty > payloadLimit
    then Left (CannotElaborate position "Implicit function type exceeds node or payload admission; use explicit {arguments}") else Right ()
  if any (\term => typeNodes term > inferredParameterNodes || payloadSize term > payloadLimit) given
    then Left (CannotElaborate position "Explicit implicit argument exceeds node or payload admission during inference") else Right ()
  opened <- openImplicitRaw position count 0 ty (\i => Just (Right i))
  Right (ImplicitConstraints count ty opened (seedImplicit 0 given) implicitConstraintBudget 0)

public export
implicitSolved : ImplicitState n -> Bool
implicitSolved state = length state.solutions == state.count

||| A missing proposal skips only this constraint, never creates a core hole.
public export
advanceImplicit : Position -> ImplicitState n -> Maybe (Term n) -> Either ResolveError (ImplicitState n)
advanceImplicit position state proposed = do
  if state.steps >= implicitTelescopeLimit
    then Left (CannotElaborate position "Implicit inference telescope admission exhausted (64)") else Right ()
  case state.problem of
    Prepared (Pi _ domain rest) mapping => do
      (solutions, budget) <- the (Either ResolveError (Solutions n, Nat)) $ case proposed of
        Nothing => Right (state.solutions, state.remainingWork)
        Just actual => do
          if typeNodes actual > inferredParameterNodes || payloadSize actual > payloadLimit
            then Left (CannotElaborate position "Implicit argument type exceeds node or payload admission; use explicit {arguments}") else Right ()
          let work = constraintCost domain actual
          if work > state.remainingWork
            then Left (CannotElaborate position "Implicit constraint work admission exhausted; use explicit {arguments}") else Right ()
          found <- case match position mapping Just domain actual state.solutions of
            Left _ => implicitFailure position
            Right found => Right found
          Right (found, minus state.remainingWork work)
      Right (ImplicitConstraints state.count state.signature (Prepared rest (skipExplicit mapping)) solutions budget (S state.steps))
    _ => implicitFailure position

||| Finish only at the complete authored spine; expected is never an
||| intermediate application's expected type.
public export
finishImplicit : Position -> Context n -> ImplicitState n -> Maybe (Term n) -> Either ResolveError (List (Term n))
finishImplicit position context state expected = do
  let solved = arguments position state.count 0 state.solutions
  solutions <- case solved of
    Right _ => Right state.solutions
    Left _ => case (expected, state.problem) of
      (Nothing, _) => Left (CannotElaborate position "Implicit arguments are ambiguous; use explicit {arguments}")
      (Just result, Prepared remaining mapping) => do
        if typeNodes result > inferredParameterNodes || payloadSize result > payloadLimit
          then Left (CannotElaborate position "Expected implicit result exceeds node or payload admission; use explicit {arguments}") else Right ()
        if constraintCost remaining result > state.remainingWork
          then Left (CannotElaborate position "Implicit constraint work admission exhausted; use explicit {arguments}") else Right ()
        case match position mapping Just remaining result state.solutions of
          Left _ => implicitFailure position
          Right found => Right found
  values <- case arguments position state.count 0 solutions of
    Left _ => Left (CannotElaborate position "Implicit arguments are ambiguous; use explicit {arguments}")
    Right values => Right values
  let size = foldl (\accum, value => min 513 (accum + 1 + typeNodes value)) 0 values
  let payload = foldl (\accum, value => min (S payloadLimit) (accum + payloadSize value)) 0 values
  if size > inferredParameterNodes || payload > payloadLimit
    then Left (CannotElaborate position "Implicit solutions exceed node or payload admission; use explicit {arguments}") else Right ()
  checkImplicitDomains position context state.signature values
  Right values

||| Infer only a leading erased prefix, from structural type constraints.
||| Phantom, conflicting, local-dependent and higher-order inversions fail closed.
public export
instantiateParameters : Position -> Nat -> Context n -> Term n -> Term n -> Either ResolveError (Term n)
instantiateParameters position fields context constructor scrutinee = do
  ty <- case inferErased checkingDepth typeReductionFuel context constructor of
    Left err => Left (CannotElaborate position ("Cannot infer constructor signature: " ++ show err))
    Right ty => Right ty
  count <- piCount position checkingDepth ty
  if count <= fields then Right constructor else do
    let params = minus count fields
    Prepared template mapping <- openParameters position params fields 0 ty (\i => Just (Right i))
    actual <- case inferErased checkingDepth typeReductionFuel context scrutinee of
      Left err => Left (CannotElaborate position ("Cannot infer pattern scrutinee type: " ++ show err))
      Right ty => normalType position ty
    template <- normalType position template
    solutions <- match position mapping Just template actual []
    values <- arguments position params 0 solutions
    let size = foldl (\accum, value => min 513 (accum + 1 + typeNodes value)) 0 values
    if size > inferredParameterNodes
       then Left (CannotElaborate position "Inferred constructor arguments exceed 512 nodes; supply parameters explicitly") else Right ()
    Right (foldl Apply constructor values)
