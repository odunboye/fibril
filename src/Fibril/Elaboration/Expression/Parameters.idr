-- Bounded first-order inference of erased constructor-prefix arguments.
-- Metavariables live only in this elaborator's scope map, never in core terms.
module Fibril.Elaboration.Expression.Parameters

import Data.Fin
import Data.List
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Data.Bytes
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

bindMetaGlobals : GlobalContext -> Position -> Nat -> Term base -> Solutions base -> Either ResolveError (Solutions base)
bindMetaGlobals shared position meta value solutions = case lookup meta solutions of
  Nothing => Right ((meta, value) :: solutions)
  Just previous => if guardedEqualGlobals shared typeReductionFuel previous value
    then Right solutions
    else Left (CannotElaborate position "Parameter consistency comparison failed or was inconclusive; supply parameters explicitly")

mutual
  matchGlobals : GlobalContext -> Position -> ScopeMap m a -> (Fin a -> Maybe (Fin base)) ->
          Term m -> Term a -> Solutions base -> Either ResolveError (Solutions base)
  matchGlobals shared position mapping prune (Variable i) value solutions = case mapping i of
    Just (Left meta) => case thin prune value of
      Nothing => failure position
      Just value => bindMetaGlobals shared position meta value solutions
    Just (Right expected) => case value of
      Variable actual => if expected == actual then Right solutions else failure position
      _ => failure position
    Nothing => failure position
  matchGlobals shared position mapping prune (GlobalRef x) (GlobalRef y) solutions =
    if x == y then Right solutions else failure position
  matchGlobals shared position mapping prune (Universe x) (Universe y) solutions =
    if x == y then Right solutions else failure position
  matchGlobals shared position mapping prune UnitType UnitType solutions = Right solutions
  matchGlobals shared position mapping prune UnitValue UnitValue solutions = Right solutions
  matchGlobals shared position mapping prune BoolType BoolType solutions = Right solutions
  matchGlobals shared position mapping prune BoolTrue BoolTrue solutions = Right solutions
  matchGlobals shared position mapping prune BoolFalse BoolFalse solutions = Right solutions
  matchGlobals shared position mapping prune NatType NatType solutions = Right solutions
  matchGlobals shared position mapping prune NatZero NatZero solutions = Right solutions
  matchGlobals shared position mapping prune (NatSucc x) (NatSucc y) solutions = matchGlobals shared position mapping prune x y solutions
  matchGlobals shared position mapping prune (NatRec p z s x) (NatRec q w t y) solutions = do
    solutions <- tripleGlobals shared position mapping prune p z s q w t solutions
    matchGlobals shared position mapping prune x y solutions
  matchGlobals shared position mapping prune (NatRecRuntime p z s x) (NatRecRuntime q w t y) solutions = do
    solutions <- tripleGlobals shared position mapping prune p z s q w t solutions
    matchGlobals shared position mapping prune x y solutions
  matchGlobals shared position mapping prune (RecType key) (RecType other) solutions =
    if key == other then Right solutions else failure position
  matchGlobals shared position mapping prune (RecEnd ty) (RecEnd other) solutions = matchGlobals shared position mapping prune ty other solutions
  matchGlobals shared position mapping prune (RecMore ty x) (RecMore other y) solutions = pairGlobals shared position mapping prune ty x other y solutions
  matchGlobals shared position mapping prune (RecFold p z s x) (RecFold q w t y) solutions = do
    solutions <- tripleGlobals shared position mapping prune p z s q w t solutions
    matchGlobals shared position mapping prune x y solutions
  matchGlobals shared position mapping prune (RecCase p x z s) (RecCase q y w t) solutions = do
    solutions <- tripleGlobals shared position mapping prune p x z q y w solutions
    matchGlobals shared position mapping prune s t solutions
  matchGlobals shared position mapping prune (NatCase p x z s) (NatCase q y w t) solutions = do
    solutions <- tripleGlobals shared position mapping prune p x z q y w solutions
    matchGlobals shared position mapping prune s t solutions
  matchGlobals shared position mapping prune (SeqCase p x z s) (SeqCase q y w t) solutions = do
    solutions <- tripleGlobals shared position mapping prune p x z q y w solutions
    matchGlobals shared position mapping prune s t solutions
  matchGlobals shared position mapping prune (SeqType key a) (SeqType other b) solutions =
    if key == other then matchGlobals shared position mapping prune a b solutions else failure position
  matchGlobals shared position mapping prune (SeqNil ty) (SeqNil other) solutions = matchGlobals shared position mapping prune ty other solutions
  matchGlobals shared position mapping prune (SeqCons ty h t) (SeqCons other x y) solutions = tripleGlobals shared position mapping prune ty h t other x y solutions
  matchGlobals shared position mapping prune (SeqFold p z s x) (SeqFold q w t y) solutions = do
    solutions <- tripleGlobals shared position mapping prune p z s q w t solutions
    matchGlobals shared position mapping prune x y solutions
  matchGlobals shared position mapping prune (IterateBinary s r n f x) (IterateBinary t u m g y) solutions = do
    solutions <- tripleGlobals shared position mapping prune s r n t u m solutions
    solutions <- matchGlobals shared position mapping prune f g solutions
    matchGlobals shared position mapping prune x y solutions
  matchGlobals shared position mapping prune (ReadBytes x) (ReadBytes y) solutions = matchGlobals shared position mapping prune x y solutions
  matchGlobals shared position mapping prune (WriteBytes x) (WriteBytes y) solutions = matchGlobals shared position mapping prune x y solutions
  matchGlobals shared position mapping prune RejectBytes RejectBytes solutions = Right solutions
  matchGlobals shared position mapping prune FlushBytes FlushBytes solutions = Right solutions
  matchGlobals shared position mapping prune ReadLine ReadLine solutions = Right solutions
  matchGlobals shared position mapping prune (FileHandleValue left first) (FileHandleValue right second) solutions =
    if left == right && first == second then Right solutions else failure position
  matchGlobals shared position mapping prune (ReadInputFile left) (ReadInputFile right) solutions = matchGlobals shared position mapping prune left right solutions
  matchGlobals shared position mapping prune (BytesLengthIs a b) (BytesLengthIs c d) solutions = pairGlobals shared position mapping prune a b c d solutions
  matchGlobals shared position mapping prune (BytesIndex a b) (BytesIndex c d) solutions = pairGlobals shared position mapping prune a b c d solutions
  matchGlobals shared position mapping prune (BytesSlice a b c) (BytesSlice d e f) solutions = tripleGlobals shared position mapping prune a b c d e f solutions
  matchGlobals shared position mapping prune (UTF8Encode x) (UTF8Encode y) solutions = matchGlobals shared position mapping prune x y solutions
  matchGlobals shared position mapping prune (UTF8Decode x) (UTF8Decode y) solutions = matchGlobals shared position mapping prune x y solutions
  matchGlobals shared position mapping prune BytesType BytesType solutions = Right solutions
  matchGlobals shared position mapping prune (BytesValue x) (BytesValue y) solutions = if x == y then Right solutions else failure position
  matchGlobals shared position mapping prune (BytesShare x) (BytesShare y) solutions = matchGlobals shared position mapping prune x y solutions
  matchGlobals shared position mapping prune (BytesLength x) (BytesLength y) solutions = matchGlobals shared position mapping prune x y solutions
  matchGlobals shared position mapping prune (BytesOctet x) (BytesOctet y) solutions = matchGlobals shared position mapping prune x y solutions
  matchGlobals shared position mapping prune (BytesAppend x y) (BytesAppend u v) solutions = pairGlobals shared position mapping prune x y u v solutions
  matchGlobals shared position mapping prune (WithRegion x y) (WithRegion u v) solutions = pairGlobals shared position mapping prune x y u v solutions
  matchGlobals shared position mapping prune StringType StringType solutions = Right solutions
  matchGlobals shared position mapping prune (StringValue x) (StringValue y) solutions =
    if x == y then Right solutions else failure position
  matchGlobals shared position mapping prune (BoxType q x) (BoxType r y) solutions =
    if q == r then matchGlobals shared position mapping prune x y solutions else failure position
  matchGlobals shared position mapping prune (Prim a xs) (Prim b ys) solutions =
    if a == b then matchTermsGlobals shared position mapping prune xs ys solutions else failure position
  matchGlobals shared position mapping prune (NominalType key xs shape) (NominalType other ys actualShape) solutions =
    if key == other then do
      solutions <- matchTermsGlobals shared position mapping prune xs ys solutions
      matchGlobals shared position mapping prune shape actualShape solutions
    else failure position
  matchGlobals shared position mapping prune (VariantType xs) (VariantType ys) solutions = matchArmsGlobals shared position mapping prune xs ys solutions
  matchGlobals shared position mapping prune (WithInputFile a p f) (WithInputFile b q g) solutions = do
    first <- matchGlobals shared position mapping prune a b solutions
    second <- matchGlobals shared position mapping prune p q first
    matchGlobals shared position mapping prune f g second
  matchGlobals shared position mapping prune (IOType x) (IOType y) solutions = matchGlobals shared position mapping prune x y solutions
  matchGlobals shared position mapping prune (FileHandleType x) (FileHandleType y) solutions = matchGlobals shared position mapping prune x y solutions
  matchGlobals shared position mapping prune (IOPure x) (IOPure y) solutions = matchGlobals shared position mapping prune x y solutions
  matchGlobals shared position mapping prune (WriteLine x) (WriteLine y) solutions = matchGlobals shared position mapping prune x y solutions
  matchGlobals shared position mapping prune (BoxValue x y) (BoxValue u v) solutions = pairGlobals shared position mapping prune x y u v solutions
  matchGlobals shared position mapping prune (Apply x y) (Apply u v) solutions = pairGlobals shared position mapping prune x y u v solutions
  matchGlobals shared position mapping prune (StringAppend x y) (StringAppend u v) solutions = pairGlobals shared position mapping prune x y u v solutions
  matchGlobals shared position mapping prune (StringEqual x y) (StringEqual u v) solutions = pairGlobals shared position mapping prune x y u v solutions
  matchGlobals shared position mapping prune (UnitCase x y) (UnitCase u v) solutions = pairGlobals shared position mapping prune x y u v solutions
  matchGlobals shared position mapping prune (BoolCase x y z) (BoolCase u v w) solutions = tripleGlobals shared position mapping prune x y z u v w solutions
  matchGlobals shared position mapping prune (BoxCase x y z) (BoxCase u v w) solutions = tripleGlobals shared position mapping prune x y z u v w solutions
  matchGlobals shared position mapping prune (PairValue x y z) (PairValue u v w) solutions = tripleGlobals shared position mapping prune x y z u v w solutions
  matchGlobals shared position mapping prune (PairCase x y z) (PairCase u v w) solutions = tripleGlobals shared position mapping prune x y z u v w solutions
  matchGlobals shared position mapping prune (IOBind x y z w) (IOBind u v a b) solutions = do
    solutions <- tripleGlobals shared position mapping prune x y z u v a solutions
    matchGlobals shared position mapping prune w b solutions
  matchGlobals shared position mapping prune (Pi q x y) (Pi r u v) solutions =
    if q == r then binderGlobals shared position mapping prune x y u v solutions else failure position
  matchGlobals shared position mapping prune (Lambda q x y) (Lambda r u v) solutions =
    if q == r then binderGlobals shared position mapping prune x y u v solutions else failure position
  matchGlobals shared position mapping prune (Sigma q r x y) (Sigma s t u v) solutions =
    if q == s && r == t then binderGlobals shared position mapping prune x y u v solutions else failure position
  matchGlobals shared position mapping prune _ _ solutions = failure position

  matchTermsGlobals : GlobalContext -> Position -> ScopeMap m a -> (Fin a -> Maybe (Fin base)) -> List (Term m) -> List (Term a) -> Solutions base -> Either ResolveError (Solutions base)
  matchTermsGlobals shared position mapping prune [] [] solutions = Right solutions
  matchTermsGlobals shared position mapping prune (x :: xs) (y :: ys) solutions = do
    solutions <- matchGlobals shared position mapping prune x y solutions
    matchTermsGlobals shared position mapping prune xs ys solutions
  matchTermsGlobals shared position mapping prune _ _ solutions = failure position

  matchArmsGlobals : GlobalContext -> Position -> ScopeMap m a -> (Fin a -> Maybe (Fin base)) -> List (Maybe (Quantity, Term m)) -> List (Maybe (Quantity, Term a)) -> Solutions base -> Either ResolveError (Solutions base)
  matchArmsGlobals shared position mapping prune [] [] solutions = Right solutions
  matchArmsGlobals shared position mapping prune (Nothing :: xs) (Nothing :: ys) solutions = matchArmsGlobals shared position mapping prune xs ys solutions
  matchArmsGlobals shared position mapping prune (Just (q, x) :: xs) (Just (r, y) :: ys) solutions =
    if q == r then do
      solutions <- matchGlobals shared position mapping prune x y solutions
      matchArmsGlobals shared position mapping prune xs ys solutions
    else failure position
  matchArmsGlobals shared position mapping prune _ _ solutions = failure position

  pairGlobals : GlobalContext -> Position -> ScopeMap m a -> (Fin a -> Maybe (Fin base)) ->
         Term m -> Term m -> Term a -> Term a -> Solutions base -> Either ResolveError (Solutions base)
  pairGlobals shared position mapping prune x y u v solutions = do
    solutions <- matchGlobals shared position mapping prune x u solutions
    matchGlobals shared position mapping prune y v solutions

  tripleGlobals : GlobalContext -> Position -> ScopeMap m a -> (Fin a -> Maybe (Fin base)) ->
           Term m -> Term m -> Term m -> Term a -> Term a -> Term a ->
           Solutions base -> Either ResolveError (Solutions base)
  tripleGlobals shared position mapping prune x y z u v w solutions = do
    solutions <- pairGlobals shared position mapping prune x y u v solutions
    matchGlobals shared position mapping prune z w solutions

  binderGlobals : GlobalContext -> Position -> ScopeMap m a -> (Fin a -> Maybe (Fin base)) ->
           Term m -> Term (S m) -> Term a -> Term (S a) ->
           Solutions base -> Either ResolveError (Solutions base)
  binderGlobals shared position mapping prune x y u v solutions = do
    solutions <- matchGlobals shared position mapping prune x u solutions
    matchGlobals shared position (liftMap mapping) (liftPrune prune) y v solutions

exposeGlobals : GlobalContext -> Position -> Term n -> Either ResolveError (Term n)
exposeGlobals shared position ty = case weakHeadGlobals (globalValue shared) typeReductionFuel ty of
  HeadForm result => Right result
  HeadLimit _ => Left (CannotElaborate position "Constructor parameter inference exhausted its reduction budget")

piCountGlobals : GlobalContext -> Position -> Nat -> Term n -> Either ResolveError Nat
piCountGlobals shared position Z ty = Left (CannotElaborate position "Constructor parameter telescope depth exhausted")
piCountGlobals shared position (S fuel) ty = do
  ty <- exposeGlobals shared position ty
  case ty of
    Pi _ _ body => S <$> piCountGlobals shared position fuel body
    _ => Right 0

data Problem : Nat -> Type where
  Prepared : Term m -> ScopeMap m base -> Problem base

openFieldsGlobals : GlobalContext -> Position -> Nat -> Term m -> ScopeMap m base -> Either ResolveError (Problem base)
openFieldsGlobals shared position Z ty mapping = Right (Prepared ty mapping)
openFieldsGlobals shared position (S fields) ty mapping = do
  ty <- exposeGlobals shared position ty
  case ty of
    Pi _ _ rest =>
      let next : ScopeMap (S m) base
          next FZ = Nothing
          next (FS i) = mapping i
       in openFieldsGlobals shared position fields rest next
    _ => failure position

openParametersGlobals : GlobalContext -> Position -> Nat -> Nat -> Nat -> Term m -> ScopeMap m base ->
                 Either ResolveError (Problem base)
openParametersGlobals shared position Z fields index ty mapping = openFieldsGlobals shared position fields ty mapping
openParametersGlobals shared position (S params) fields index ty mapping = do
  ty <- exposeGlobals shared position ty
  case ty of
    Pi Erased _ rest =>
      let next : ScopeMap (S m) base
          next FZ = Just (Left index)
          next (FS i) = mapping i
       in openParametersGlobals shared position params fields (S index) rest next
    _ => failure position

normalTypeGlobals : GlobalContext -> Position -> Term n -> Either ResolveError (Term n)
normalTypeGlobals shared position ty = do
  if typeNodes ty > inferredParameterNodes
     then Left (CannotElaborate position "Constructor parameter inference types exceed 512 nodes; supply parameters explicitly") else Right ()
  normal <- case normalizeGlobals (globalValue shared) typeReductionFuel ty of
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
implicitArgumentTypeGlobals : GlobalContext -> Position -> Nat -> Context n -> Term n -> Either ResolveError (Maybe (Term n))
implicitArgumentTypeGlobals shared position Z context _ = Left (CannotElaborate position "Implicit argument type proposal depth exhausted; use explicit {arguments}")
implicitArgumentTypeGlobals shared position (S fuel) context (GlobalRef key) =
  case globalEntry shared key of
    Just (_, ty, _) => Right (Just (rename absurd ty))
    Nothing => Left (CannotElaborate position "Unknown shared global in implicit argument")
implicitArgumentTypeGlobals shared position (S fuel) context (Variable index) = Just <$> lookupImplicitType position implicitTelescopeLimit id context index
implicitArgumentTypeGlobals shared position (S fuel) context (BytesValue _) = Right (Just BytesType)
implicitArgumentTypeGlobals shared position (S fuel) context (BytesLengthIs _ _) = Right (Just BoolType)
implicitArgumentTypeGlobals shared position (S fuel) context (BytesIndex _ _) = Right (Just byteIndexResultType)
implicitArgumentTypeGlobals shared position (S fuel) context (BytesSlice _ _ _) = Right (Just BytesType)
implicitArgumentTypeGlobals shared position (S fuel) context (UTF8Encode _) = Right (Just (utf8ResultType BytesType))
implicitArgumentTypeGlobals shared position (S fuel) context (UTF8Decode _) = Right (Just (utf8ResultType StringType))
implicitArgumentTypeGlobals shared position (S fuel) context (IterateBinary s r _ _ _) = Right (Just (IOType (loopVariantType s r)))
implicitArgumentTypeGlobals shared position (S fuel) context (ReadBytes _) = Right (Just (IOType byteReadResultType))
implicitArgumentTypeGlobals shared position (S fuel) context (WriteBytes _) = Right (Just (IOType UnitType))
implicitArgumentTypeGlobals shared position (S fuel) context RejectBytes = Right (Just (IOType UnitType))
implicitArgumentTypeGlobals shared position (S fuel) context FlushBytes = Right (Just (IOType UnitType))
implicitArgumentTypeGlobals shared position (S fuel) context BytesType = Right (Just (Universe 0))
implicitArgumentTypeGlobals shared position (S fuel) context (WithRegion resultType _) = Right (Just resultType)
implicitArgumentTypeGlobals shared position (S fuel) context (BytesAppend _ _) = Right (Just BytesType)
implicitArgumentTypeGlobals shared position (S fuel) context (BytesOctet _) = Right (Just BytesType)
implicitArgumentTypeGlobals shared position (S fuel) context (BytesShare _) = Right (Just (BoxType Unrestricted BytesType))
implicitArgumentTypeGlobals shared position (S fuel) context (BytesLength _) = Right (Just NatType)
implicitArgumentTypeGlobals shared position (S fuel) context (StringValue _) = Right (Just StringType)
implicitArgumentTypeGlobals shared position (S fuel) context BoolTrue = Right (Just BoolType)
implicitArgumentTypeGlobals shared position (S fuel) context BoolFalse = Right (Just BoolType)
implicitArgumentTypeGlobals shared position (S fuel) context NatType = Right (Just (Universe 0))
implicitArgumentTypeGlobals shared position (S fuel) context NatZero = Right (Just NatType)
implicitArgumentTypeGlobals shared position (S fuel) context (NatSucc _) = Right (Just NatType)
implicitArgumentTypeGlobals shared position (S fuel) context (NatRec motive _ _ value) = do
  if 1 + typeNodes motive + typeNodes value > inferredParameterNodes ||
     payloadSize motive + payloadSize value > payloadLimit
    then Left (CannotElaborate position "Implicit Nat recursor result exceeds admission") else Right ()
  -- A recursor's result is P value. A raw application may not structurally
  -- match its reduced type; if bounded conversion cannot expose it, skip this
  -- proposal rather than reject later, independently checked constraints.
  case guardedNormalGlobals shared typeReductionFuel (Apply motive value) of
    Just (Apply _ _) => Right Nothing
    Just ty => Right (Just ty)
    Nothing => Right Nothing
implicitArgumentTypeGlobals shared position (S fuel) context (NatRecRuntime motive _ _ value) = do
  if 1 + typeNodes motive + typeNodes value > inferredParameterNodes ||
     payloadSize motive + payloadSize value > payloadLimit
    then Left (CannotElaborate position "Implicit Nat recursor result exceeds admission") else Right ()
  case guardedNormalGlobals shared typeReductionFuel (Apply motive value) of
    Just (Apply _ _) => Right Nothing
    Just ty => Right (Just ty)
    Nothing => Right Nothing
implicitArgumentTypeGlobals shared position (S fuel) context (RecType _) = Right (Just (Universe 0))
implicitArgumentTypeGlobals shared position (S fuel) context (RecEnd ty) = Right (Just ty)
implicitArgumentTypeGlobals shared position (S fuel) context (RecMore ty _) = Right (Just ty)
implicitArgumentTypeGlobals shared position (S fuel) context (RecFold motive _ _ value) = do
  if 1 + typeNodes motive + typeNodes value > inferredParameterNodes ||
     payloadSize motive + payloadSize value > payloadLimit
    then Left (CannotElaborate position "Implicit recursive fold result exceeds admission") else Right ()
  case guardedNormalGlobals shared typeReductionFuel (Apply motive value) of
    Just (Apply _ _) => Right Nothing
    Just ty => Right (Just ty)
    Nothing => Right Nothing
implicitArgumentTypeGlobals shared position (S fuel) context (RecCase motive value _ _) = do
  if 1 + typeNodes motive + typeNodes value > inferredParameterNodes ||
     payloadSize motive + payloadSize value > payloadLimit
    then Left (CannotElaborate position "Implicit recursive case result exceeds admission") else Right ()
  case guardedNormalGlobals shared typeReductionFuel (Apply motive value) of
    Just (Apply _ _) => Right Nothing
    Just ty => Right (Just ty)
    Nothing => Right Nothing
implicitArgumentTypeGlobals shared position (S fuel) context (NatCase motive value _ _) = do
  if 1 + typeNodes motive + typeNodes value > inferredParameterNodes ||
     payloadSize motive + payloadSize value > payloadLimit
    then Left (CannotElaborate position "Implicit Nat case result exceeds admission") else Right ()
  case guardedNormalGlobals shared typeReductionFuel (Apply motive value) of
    Just (Apply _ _) => Right Nothing
    Just ty => Right (Just ty)
    Nothing => Right Nothing
implicitArgumentTypeGlobals shared position (S fuel) context (SeqCase motive value _ _) = do
  if 1 + typeNodes motive + typeNodes value > inferredParameterNodes ||
     payloadSize motive + payloadSize value > payloadLimit
    then Left (CannotElaborate position "Implicit sequence case result exceeds admission") else Right ()
  case guardedNormalGlobals shared typeReductionFuel (Apply motive value) of
    Just (Apply _ _) => Right Nothing
    Just ty => Right (Just ty)
    Nothing => Right Nothing
implicitArgumentTypeGlobals shared position (S fuel) context (SeqType _ _) = Right (Just (Universe 0))
implicitArgumentTypeGlobals shared position (S fuel) context (SeqNil ty) = Right (Just ty)
implicitArgumentTypeGlobals shared position (S fuel) context (SeqCons ty _ _) = Right (Just ty)
implicitArgumentTypeGlobals shared position (S fuel) context (SeqFold motive _ _ value) = do
  if 1 + typeNodes motive + typeNodes value > inferredParameterNodes ||
     payloadSize motive + payloadSize value > payloadLimit
    then Left (CannotElaborate position "Implicit sequence fold result exceeds admission") else Right ()
  case guardedNormalGlobals shared typeReductionFuel (Apply motive value) of
    Just (Apply _ _) => Right Nothing
    Just ty => Right (Just ty)
    Nothing => Right Nothing
implicitArgumentTypeGlobals shared position (S fuel) context ReadLine = Right (Just (IOType readResultType))
implicitArgumentTypeGlobals shared position (S fuel) context (FileHandleValue identity _) = Right (Just (FileHandleType (runtimeFileRegion identity)))
implicitArgumentTypeGlobals shared position (S fuel) context UnitValue = Right (Just UnitType)
implicitArgumentTypeGlobals shared position (S fuel) context StringType = Right (Just (Universe 0))
implicitArgumentTypeGlobals shared position (S fuel) context BoolType = Right (Just (Universe 0))
implicitArgumentTypeGlobals shared position (S fuel) context UnitType = Right (Just (Universe 0))
implicitArgumentTypeGlobals shared position (S fuel) context (Universe level) = Right (Just (Universe (S level)))
implicitArgumentTypeGlobals shared position (S fuel) context (Prim WordTypeOp _) = Right (Just (Universe 0))
implicitArgumentTypeGlobals shared position (S fuel) context (Prim (WordLitOp _) _) = Right (Just (Prim WordTypeOp []))
implicitArgumentTypeGlobals shared position (S fuel) context (Prim op _) = Right (wordBinaryResult op)
implicitArgumentTypeGlobals shared position (S fuel) context (StringAppend _ _) = Right (Just StringType)
implicitArgumentTypeGlobals shared position (S fuel) context (StringEqual _ _) = Right (Just BoolType)
implicitArgumentTypeGlobals shared position (S fuel) context (NominalValue ty _) = Right (Just ty)
implicitArgumentTypeGlobals shared position (S fuel) context (VariantValue ty _ _) = Right (Just ty)
implicitArgumentTypeGlobals shared position (S fuel) context (BoxValue ty _) = Right (Just ty)
implicitArgumentTypeGlobals shared position (S fuel) context (PairValue ty _ _) = Right (Just ty)
implicitArgumentTypeGlobals shared position (S fuel) context (UnitCase _ body) = implicitArgumentTypeGlobals shared position fuel context body
implicitArgumentTypeGlobals shared position (S fuel) context (BoolCase _ yes _) = implicitArgumentTypeGlobals shared position fuel context yes
-- This proposes an annotation only; the original application remains checked.
implicitArgumentTypeGlobals shared position (S fuel) context (Apply (Lambda _ domain (Variable FZ)) _) = Right (Just domain)
implicitArgumentTypeGlobals shared position (S fuel) context (Pi q domain body) = do
  if typeNodes domain > inferredParameterNodes || payloadSize domain > payloadLimit
    then Left (CannotElaborate position "Implicit Pi domain exceeds admission") else Right ()
  domainType <- implicitArgumentTypeGlobals shared position fuel context domain
  bodyType <- implicitArgumentTypeGlobals shared position fuel (Extend context q domain) body
  case (domainType, bodyType) of
    (Just (Universe left), Just (Universe right)) => Right (Just (Universe (max left right)))
    _ => Right Nothing
implicitArgumentTypeGlobals shared position (S fuel) context (Lambda q domain body) = do
  if typeNodes domain > inferredParameterNodes || payloadSize domain > payloadLimit
    then Left (CannotElaborate position "Implicit lambda domain exceeds admission") else Right ()
  result <- implicitArgumentTypeGlobals shared position fuel (Extend context q domain) body
  case result of
    Nothing => Right Nothing
    Just ty => do
      if 1 + typeNodes domain + typeNodes ty > inferredParameterNodes ||
         payloadSize domain + payloadSize ty > payloadLimit
        then Left (CannotElaborate position "Implicit lambda type exceeds admission") else Right ()
      Right (Just (Pi q domain ty))
implicitArgumentTypeGlobals shared position (S fuel) context (Apply function argument) = do
  proposed <- implicitArgumentTypeGlobals shared position fuel context function
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
implicitArgumentTypeGlobals shared position (S fuel) context _ = Right Nothing


checkImplicitDomainsGlobals : GlobalContext -> Position -> Context n -> Term n -> List (Term n) -> Either ResolveError ()
checkImplicitDomainsGlobals shared position context ty [] = Right ()
checkImplicitDomainsGlobals shared position context (Pi Erased domain rest) (solution :: remaining) = do
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
      checkImplicitDomainsGlobals shared position context (instantiateTerm solution rest) remaining
checkImplicitDomainsGlobals shared position context _ _ = implicitFailure position

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
advanceImplicitGlobals : GlobalContext -> Position -> ImplicitState n -> Maybe (Term n) -> Either ResolveError (ImplicitState n)
advanceImplicitGlobals shared position state proposed = do
  if state.steps >= implicitTelescopeLimit
    then Left (CannotElaborate position "Implicit inference telescope admission exhausted (64)") else Right ()
  case state.problem of
    Prepared (Pi _ domain rest) mapping => do
      (solutions, budget) <- the (Either ResolveError (Solutions n, Nat)) $ case proposed of
        Nothing => Right (state.solutions, state.remainingWork)
        Just actual => do
          if typeNodes actual > inferredParameterNodes || payloadSize actual > payloadLimit
            then Left (CannotElaborate position "Implicit argument type exceeds node or payload admission; use explicit {arguments}") else Right ()
          domain <- normalTypeGlobals shared position domain
          actual <- normalTypeGlobals shared position actual
          let work = constraintCost domain actual
          if work > state.remainingWork
            then Left (CannotElaborate position "Implicit constraint work admission exhausted; use explicit {arguments}") else Right ()
          found <- case matchGlobals shared position mapping Just domain actual state.solutions of
            Left _ => implicitFailure position
            Right found => Right found
          Right (found, minus state.remainingWork work)
      Right (ImplicitConstraints state.count state.signature (Prepared rest (skipExplicit mapping)) solutions budget (S state.steps))
    _ => implicitFailure position

||| Finish only at the complete authored spine; expected is never an
||| intermediate application's expected type.
public export
finishImplicitGlobals : GlobalContext -> Position -> Context n -> ImplicitState n -> Maybe (Term n) -> Either ResolveError (List (Term n))
finishImplicitGlobals shared position context state expected = do
  let solved = arguments position state.count 0 state.solutions
  solutions <- case solved of
    Right _ => Right state.solutions
    Left _ => case (expected, state.problem) of
      (Nothing, _) => Left (CannotElaborate position "Implicit arguments are ambiguous; use explicit {arguments}")
      (Just result, Prepared remaining mapping) => do
        if typeNodes result > inferredParameterNodes || payloadSize result > payloadLimit
          then Left (CannotElaborate position "Expected implicit result exceeds node or payload admission; use explicit {arguments}") else Right ()
        remaining <- normalTypeGlobals shared position remaining
        result <- normalTypeGlobals shared position result
        if constraintCost remaining result > state.remainingWork
          then Left (CannotElaborate position "Implicit constraint work admission exhausted; use explicit {arguments}") else Right ()
        case matchGlobals shared position mapping Just remaining result state.solutions of
          Left _ => implicitFailure position
          Right found => Right found
  values <- case arguments position state.count 0 solutions of
    Left _ => Left (CannotElaborate position "Implicit arguments are ambiguous; use explicit {arguments}")
    Right values => Right values
  let size = foldl (\accum, value => min 513 (accum + 1 + typeNodes value)) 0 values
  let payload = foldl (\accum, value => min (S payloadLimit) (accum + payloadSize value)) 0 values
  if size > inferredParameterNodes || payload > payloadLimit
    then Left (CannotElaborate position "Implicit solutions exceed node or payload admission; use explicit {arguments}") else Right ()
  checkImplicitDomainsGlobals shared position context state.signature values
  Right values

||| Infer only a leading erased prefix, from structural type constraints.
||| Phantom, conflicting, local-dependent and higher-order inversions fail closed.
public export
instantiateParametersGlobals : GlobalContext -> Position -> Nat -> Context n -> Term n -> Term n -> Either ResolveError (Term n)
instantiateParametersGlobals shared position fields context constructor scrutinee = do
  ty <- case inferErasedGlobals shared checkingDepth typeReductionFuel context constructor of
    Left err => Left (CannotElaborate position ("Cannot infer constructor signature: " ++ show err))
    Right ty => Right ty
  count <- piCountGlobals shared position checkingDepth ty
  if count <= fields then Right constructor else do
    let params = minus count fields
    Prepared template mapping <- openParametersGlobals shared position params fields 0 ty (\i => Just (Right i))
    actual <- case inferErasedGlobals shared checkingDepth typeReductionFuel context scrutinee of
      Left err => Left (CannotElaborate position ("Cannot infer pattern scrutinee type: " ++ show err))
      Right ty => normalTypeGlobals shared position ty
    template <- normalTypeGlobals shared position template
    solutions <- matchGlobals shared position mapping Just template actual []
    values <- arguments position params 0 solutions
    let size = foldl (\accum, value => min 513 (accum + 1 + typeNodes value)) 0 values
    if size > inferredParameterNodes
       then Left (CannotElaborate position "Inferred constructor arguments exceed 512 nodes; supply parameters explicitly") else Right ()
    Right (foldl Apply constructor values)

-- Closed-syntax compatibility APIs. Shared programs pass their checked context explicitly.
public export
advanceImplicit : Position -> ImplicitState n -> Maybe (Term n) -> Either ResolveError (ImplicitState n)
advanceImplicit = advanceImplicitGlobals emptyGlobals

public export
finishImplicit : Position -> Context n -> ImplicitState n -> Maybe (Term n) -> Either ResolveError (List (Term n))
finishImplicit = finishImplicitGlobals emptyGlobals

public export
implicitArgumentType : Position -> Nat -> Context n -> Term n -> Either ResolveError (Maybe (Term n))
implicitArgumentType = implicitArgumentTypeGlobals emptyGlobals

public export
instantiateParameters : Position -> Nat -> Context n -> Term n -> Term n -> Either ResolveError (Term n)
instantiateParameters = instantiateParametersGlobals emptyGlobals
