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
  match position mapping prune (IOType x) (IOType y) solutions = match position mapping prune x y solutions
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

||| Infer one checked erased leading argument from the next explicit argument's
||| synthesized type. This produces an ordinary term, not a core metavariable.
public export
inferLeadingArgument : Position -> Context n -> Term n -> Term n -> Either ResolveError (Term n)
inferLeadingArgument position context ty argument = do
  if typeNodes ty > inferredParameterNodes
    then Left (CannotElaborate position "Implicit function type exceeds 512 nodes; use an explicit {argument}") else Right ()
  actual <- case inferErased checkingDepth typeReductionFuel context argument of
    Left err => Left (CannotElaborate position ("Cannot infer explicit argument type: " ++ show err ++ "; use an explicit {argument}"))
    Right actual => Right actual
  if typeNodes actual > inferredParameterNodes
    then Left (CannotElaborate position "Implicit argument type exceeds 512 nodes; use an explicit {argument}") else Right ()
  case ty of
    Pi Erased domain (Pi _ template _) => do
      let mapping : ScopeMap (S n) n
          mapping FZ = Just (Left 0)
          mapping (FS i) = Just (Right i)
      solutions <- case match position mapping Just template actual [] of
        Left _ => Left (CannotElaborate position "Cannot infer implicit argument from this argument type; use an explicit {argument}")
        Right solutions => Right solutions
      solution <- case lookup (the Nat 0) solutions of
        Nothing => Left (CannotElaborate position "Implicit argument is ambiguous; use an explicit {argument}")
        Just solution => Right solution
      if typeNodes solution > inferredParameterNodes
        then Left (CannotElaborate position "Implicit solution exceeds 512 nodes; use an explicit {argument}") else Right ()
      case checkErased checkingDepth typeReductionFuel context solution domain of
        Left err => Left (CannotElaborate position ("Inferred implicit argument fails its domain: " ++ show err))
        Right () => Right solution
    _ => Left (CannotElaborate position "Implicit function needs an erased Pi followed by an explicit Pi")

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
