-- Contextual named-to-core elaboration; ordinary core checking remains independent.
module Fibril.Elaboration.Expression

import Data.Fin
import Data.List
import Data.Vect
import Fibril.Core.SharedProgram
import Fibril.Core.Size
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Global
import public Fibril.Source.Resolve.Error
import Fibril.Core.Context
import Fibril.Core.DataDecl
import Fibril.Core.Erased
import Fibril.Core.Reduction
import Fibril.Core.Limits
import Fibril.Core.WeakHead
import Fibril.Elaboration.IndexRefinement
import Fibril.Elaboration.Completion
import Fibril.Elaboration.SequenceView
import Fibril.Elaboration.DataCase
import Fibril.Elaboration.Expression.Scope
import Fibril.Elaboration.Expression.Conversion
import Fibril.Elaboration.Expression.Abstract
import Fibril.Elaboration.Expression.Payload
import Fibril.Elaboration.Expression.Motive
import Fibril.Elaboration.Expression.Constructor
import Fibril.Elaboration.Expression.Parameters
import Fibril.Elaboration.Expression.Dictionary

%default total

lookupName : String -> Vect n String -> Maybe (Fin n)
lookupName name [] = Nothing
lookupName name (bound :: rest) =
  if name == bound then Just FZ else map FS (lookupName name rest)

ambiguityMessage : String -> List String -> String
ambiguityMessage name candidates =
  "Ambiguous imported name " ++ name ++ "; candidates: " ++ concat (intersperse ", " candidates) ++ "; use a qualified name"

boundedResultGlobals : GlobalContext -> Position -> Term n -> Either ResolveError (Term n)
boundedResultGlobals shared position result = do
  if typeNodes result > inferredResultNodes then Left (CannotElaborate position "Inferred motive result type exceeds 512 nodes; use an explicit return motive") else Right ()
  normal <- case normalizeGlobals (globalValue shared) typeReductionFuel result of
    Normal value => Right value
    OutOfFuel _ => Left (CannotElaborate position "Motive inference reduction budget exhausted; use an explicit return motive")
  if typeNodes normal > inferredResultNodes then Left (CannotElaborate position "Inferred motive result type exceeds 512 nodes; use an explicit return motive") else Right normal

inferCaseGlobals : GlobalContext -> Position -> Nat -> Context n -> Term n -> Term n -> Either ResolveError (Term n)
inferCaseGlobals shared position arity context scrutinee branch = do
  branchType <- case inferErasedGlobals shared checkingDepth typeReductionFuel context branch of
    Left err => Left (CannotElaborate position ("Cannot infer record branch type: " ++ show err))
    Right ty => Right ty
  case (arity, branch, branchType) of
    (1, Lambda q domain _, Pi _ _ result) => do
      result <- boundedResultGlobals shared position result
      motive <- unaryMotive position q domain result
      Right (BoxCase motive scrutinee branch)
    (2, Lambda q domain (Lambda r second _), Pi _ _ (Pi _ _ result)) => do
      result <- boundedResultGlobals shared position result
      motive <- binaryMotive position q r domain second result
      Right (PairCase motive scrutinee branch)
    _ => Left (CannotElaborate position "Record motive inference requires one or two typed pattern binders")

||| Infer a payload-independent result, comparing by bounded guarded conversion.
||| Dependent motives are handled separately from equation expected types.
||| The independent core checker still checks the resulting complete case.
dataBranchResultGlobals : GlobalContext -> Position -> Context n -> Maybe (Quantity, Term n) -> Term n -> Either ResolveError (Term n)
dataBranchResultGlobals shared position context descriptor branch = do
  ty <- case inferErasedGlobals shared checkingDepth typeReductionFuel context branch of
    Left err => Left (CannotElaborate position ("Cannot infer data-case branch type: " ++ show err ++ "; use an explicit return motive"))
    Right ty => Right ty
  case (descriptor, ty) of
    (Nothing, result) => if typeNodes result > inferredResultNodes
      then Left (CannotElaborate position "Inferred data-case result exceeds 512 nodes; use an explicit return motive")
      else Right result
    (Just _, Pi _ _ result) => do
      if typeNodes result > inferredResultNodes
        then Left (CannotElaborate position "Inferred data-case result exceeds 512 nodes; use an explicit return motive") else Right ()
      case dropNewest result of
        Nothing => Left (CannotElaborate position "Data-case result depends on a payload; use an explicit return motive")
        Just outer => Right outer
    _ => Left (CannotElaborate position "Cannot infer data-case payload result; use an explicit return motive")

constantDataResultGlobals : GlobalContext -> Position -> Context n -> List (Maybe (Quantity, Term n)) -> List (Term n) -> Either ResolveError (Term n)
constantDataResultGlobals shared position context [] [] = Left (CannotElaborate position "Cannot infer an empty data-case result")
constantDataResultGlobals shared position context (descriptor :: descriptors) (branch :: branches) = do
  first <- dataBranchResultGlobals shared position context descriptor branch
  agree first descriptors branches
  Right first
  where
    agree : Term n -> List (Maybe (Quantity, Term n)) -> List (Term n) -> Either ResolveError ()
    agree first [] [] = Right ()
    agree first (descriptor :: descriptors) (branch :: branches) = do
      result <- dataBranchResultGlobals shared position context descriptor branch
      if guardedEqualGlobals shared typeReductionFuel first result then agree first descriptors branches
        else Left (CannotElaborate position "Data-case branch results differ or guarded conversion was inconclusive; use an explicit return motive")
    agree first _ _ = Left (CannotElaborate position "Data-case branch count does not match shape")
constantDataResultGlobals shared position context _ _ = Left (CannotElaborate position "Data-case branch count does not match shape")

||| A sequence cons branch has two payload binders; a constant result must
||| escape both, not just the most recent tail binder.
constantSequenceResultGlobals : GlobalContext -> Position -> Context n -> Term n -> Term n -> Either ResolveError (Term n)
constantSequenceResultGlobals shared position context base cons = do
  first <- dataBranchResultGlobals shared position context Nothing base
  ty <- case inferErasedGlobals shared checkingDepth typeReductionFuel context cons of
    Left err => Left (CannotElaborate position ("Cannot infer sequence-case branch type: " ++ show err ++ "; use an explicit return motive"))
    Right result => Right result
  result <- case ty of
    Pi _ _ (Pi _ _ result) => Right result
    _ => Left (CannotElaborate position "Cannot infer two sequence-case payload binders; use an explicit return motive")
  if typeNodes result > inferredResultNodes || payloadSize result > payloadLimit
    then Left (CannotElaborate position "Sequence-case result exceeds admission; use an explicit return motive") else Right ()
  one <- case dropNewest result of
    Nothing => Left (CannotElaborate position "Sequence-case result depends on the tail; use an explicit return motive")
    Just outer => Right outer
  common <- case dropNewest one of
    Nothing => Left (CannotElaborate position "Sequence-case result depends on the head; use an explicit return motive")
    Just outer => Right outer
  if guardedEqualGlobals shared typeReductionFuel first common then Right first
    else Left (CannotElaborate position "Sequence-case branch results differ or conversion was inconclusive; use an explicit return motive")

expectedDataMotive : Position -> Term n -> Term n -> Term n -> Either ResolveError (Term n)
expectedDataMotive position nominal result scrutinee = do
  let resultSize = typeNodes result
  if resultSize > inferredResultNodes
    then Left (CannotElaborate position "Expected data-case result exceeds 512 nodes; use an explicit return motive") else Right ()
  body <- case scrutinee of
    Variable index =>
      let abstract : Fin n -> Fin (S n)
          abstract i = if i == index then FZ else FS i in
        Right (rename abstract result)
    _ => do
      let targetSize = typeNodes scrutinee
      if targetSize > inferredResultNodes then Left (CannotElaborate position "Data-case scrutinee exceeds abstraction budget; use an explicit return motive") else Right ()
      let targetPayload = payloadSize scrutinee
      let resultPayload = payloadSize result
      if targetPayload > payloadLimit || resultPayload > payloadLimit ||
         (1 + targetSize + targetPayload) * (1 + resultSize + resultPayload) > 262144
        then Left (CannotElaborate position "Data-case abstraction work budget exhausted; use an explicit return motive") else Right ()
      Right (abstractOver scrutinee result)
  if typeNodes body > inferredResultNodes
    then Left (CannotElaborate position "Abstracted data-case result exceeds 512 nodes; use an explicit return motive") else Right ()
  Right (Lambda Erased nominal body)

public export
wantsExpected : Expr -> Bool
wantsExpected (NDataCase _ _ Nothing _) = True
wantsExpected (NCaseEither _ _ asData) = wantsExpected asData
wantsExpected (NLambda _ _ _ _ _) = True
wantsExpected (NLet _ _ _ _ _ _) = True
wantsExpected (NIf _ _ _ _) = True
wantsExpected (NUnitCase _ _ _) = True
wantsExpected _ = False

implicitHead : List GlobalDefinition -> Vect n String -> Expr -> Maybe GlobalDefinition
implicitHead globals env (NRef _ name) = case lookupName name env of
  Just _ => Nothing
  Nothing => case find (\entry => entry.name == name) globals of
    Just entry => if entry.implicitPrefix > 0 then Just entry else Nothing
    Nothing => Nothing
implicitHead globals env (NQualifiedRef _ name) = case find (\entry => entry.name == name) globals of
  Just entry => if entry.implicitPrefix > 0 then Just entry else Nothing
  Nothing => Nothing
implicitHead globals env _ = Nothing

implicitHeadFailure : List GlobalDefinition -> Vect n String -> Expr -> ResolveError
implicitHeadFailure globals env head = case head of
  NRef span name => case lookupName name env of
    Just _ => fallback
    Nothing => case find (\entry => entry.name == name) globals of
      Just _ => fallback
      Nothing => case qualifiedCandidates name globals of
        candidates@(_ :: _ :: _) => CannotElaborate span.start (ambiguityMessage name candidates)
        _ => fallback
  _ => fallback
  where
    fallback : ResolveError
    fallback = CannotElaborate (extent head).start "Explicit {arguments} require a direct global with an implicit prefix"

hasImplicitCall : List GlobalDefinition -> Vect n String -> Expr -> Bool
hasImplicitCall globals env source =
  let (head, arguments) = applicationSpine source in
    case arguments of
      [] => False
      _ => case implicitHead globals env head of Just _ => True; Nothing => False

spineAdmission : Position -> Nat -> List CallArgument -> Either ResolveError Bool
spineAdmission position capacity = go 0 False
  where
    go : Nat -> Bool -> List CallArgument -> Either ResolveError Bool
    go count seen [] =
      if count > capacity then Left (CannotElaborate position "Too many explicit {arguments}")
        else Right (seen && count < capacity)
    go count seen (item :: rest) = case item of
      BracedArgument span _ =>
        if seen then Left (CannotElaborate span.start "Explicit {arguments} must precede ordinary arguments")
          else go (S count) False rest
      OrdinaryArgument _ _ => go count True rest

record PendingImplicit (n : Nat) where
  constructor PendingCall
  entry : GlobalDefinition
  function : Term n
  given : List (Term n)
  ordinary : List (Term n)
  solver : Maybe (ImplicitState n)
  applied : Maybe (Term n)

namedConstructor : Expr -> Bool
namedConstructor (NRef _ _) = True
namedConstructor (NQualifiedRef _ _) = True
namedConstructor (NApply _ function _) = namedConstructor function
namedConstructor _ = False

||| The predecessor of a Nat pattern in a written `case` may be unrestricted exactly when
||| the scrutinee is a variable bound unrestricted, so its resource can be duplicated.
||| Any other scrutinee keeps the linear predecessor, and so do pattern clauses (their
||| lowered scrutinee is named $clauseScrutinee): a clause must consume its predecessor
||| exactly once. The core runtime check validates the choice either way.
predecessorQuantity : Context n -> Vect n String -> Term n -> Quantity
predecessorQuantity ctx env (Variable i) =
  if lookupQuantity i ctx == Unrestricted && index i env /= "$clauseScrutinee"
    then Unrestricted else Linear
predecessorQuantity _ _ _ = Linear

||| Number of field lambdas of a normalized curried constructor value.
constructorFieldCount : Term m -> Nat
constructorFieldCount (Lambda _ _ body) = S (constructorFieldCount body)
constructorFieldCount _ = Z

||| Fields a wildcard must destructure to drop a linear pair payload: each
||| linear tail that is itself a pair continues the record. Counting is only a
||| guide; the core checker still rejects dropping any linear field.
payloadFieldCount : Term m -> Nat
payloadFieldCount (Sigma _ r _ rest) = case (r, rest) of
  (Linear, Sigma _ _ _ _) => S (payloadFieldCount rest)
  _ => 2
payloadFieldCount _ = 1

||| Tag of a curried constructor value (any number of field lambdas).
constructorBodyTag : Term m -> Maybe Nat
constructorBodyTag (Lambda _ _ body) = constructorBodyTag body
constructorBodyTag (NominalValue _ (VariantValue _ tag (Just _))) = Just tag
constructorBodyTag _ = Nothing

mutual
  ||| Visibility is accepted only on a checked module declaration's leading
  ||| erased prefix, followed by a source-authored ordinary Pi.
  public export
  elaborateSignatureGlobals : GlobalContext -> List GlobalDefinition -> Maybe (Context n) -> Vect n String -> Expr -> Either ResolveError (Term n)
  elaborateSignatureGlobals shared globals context env signature = elaborateSignatureWithGlobals shared False globals context env signature

  ||| Only generated declarations may have an implicit-only telescope, needed
  ||| for explicitly instantiated nullary data constructors.
  public export
  elaborateSignatureWithGlobals : GlobalContext -> Bool -> List GlobalDefinition -> Maybe (Context n) -> Vect n String -> Expr -> Either ResolveError (Term n)
  elaborateSignatureWithGlobals shared allowImplicitOnly globals context env (NImplicitPi span Erased name domain body) = do
    case body of
      NImplicitPi _ _ _ _ _ => Right ()
      NPi _ _ _ _ _ => Right ()
      NConstraintPi _ _ _ _ _ => Right ()
      _ => if allowImplicitOnly then Right () else Left (CannotElaborate span.start "Implicit prefix must be followed by an explicit Pi")
    domain <- elaborateInWithGlobals shared globals context env domain
    result <- elaborateSignatureWithGlobals shared allowImplicitOnly globals (map (\ctx => Extend ctx Erased domain) context) (name :: env) body
    Right (Pi Erased domain result)
  elaborateSignatureWithGlobals shared allowImplicitOnly globals context env (NImplicitPi span _ _ _ _) =
    Left (CannotElaborate span.start "Implicit binders must have quantity 0")
  elaborateSignatureWithGlobals shared allowImplicitOnly globals context env signature = elaborateInWithGlobals shared globals context env signature

  elaborateTermsGlobals : GlobalContext -> List GlobalDefinition -> Maybe (Context n) -> Vect n String -> List Expr -> Either ResolveError (List (Term n))
  elaborateTermsGlobals shared globals context env [] = Right []
  elaborateTermsGlobals shared globals context env (x :: xs) = [| elaborateInWithGlobals shared globals context env x :: elaborateTermsGlobals shared globals context env xs |]

  dataCaseTagGlobals : GlobalContext -> Position -> Term n -> Either ResolveError Nat
  dataCaseTagGlobals shared position value = case normalizeGlobals (globalValue shared) typeReductionFuel value of
    OutOfFuel _ => Left (CannotElaborate position "Data-case constructor reduction budget exhausted")
    Normal (NominalValue _ (VariantValue _ tag Nothing)) => Right tag
    Normal (Lambda _ _ (NominalValue _ (VariantValue _ tag (Just (Variable FZ))))) => Right tag
    Normal other => case constructorBodyTag other of
      Just tag => Right tag
      Nothing => Left (CannotElaborate position "Data-case pattern must name a transparent constructor value")

  ||| A constructor applied to the scrutinee's parameters, normalized, must be a
  ||| curried lambda of exactly `arity` fields that builds this nominal type and
  ||| shape; its tag is returned. Unary and nullary arms keep their exact-form comparison.
  multiFieldConstructorTag : GlobalContext -> Position -> Nat -> Term m -> Term m -> Term m -> Either ResolveError Nat
  multiFieldConstructorTag shared position arity nominal shape candidate =
    case normalizeGlobals (globalValue shared) typeReductionFuel candidate of
      OutOfFuel _ => Left (CannotElaborate position "Data-case constructor reduction budget exhausted")
      Normal normal => go arity nominal shape normal
    where
      go : Nat -> Term k -> Term k -> Term k -> Either ResolveError Nat
      go (S fields) nominal shape (Lambda _ _ body) = go fields (weaken nominal) (weaken shape) body
      go Z nominal shape (NominalValue actualNominal (VariantValue actualShape tag (Just _))) =
        case (betaCompareGlobals (globalValue shared) typeReductionFuel actualNominal nominal,
              betaCompareGlobals (globalValue shared) typeReductionFuel actualShape shape) of
          (EqualNormalForms, EqualNormalForms) => Right tag
          (Inconclusive, _) => Left (CannotElaborate position "Data-case constructor comparison budget exhausted")
          (_, Inconclusive) => Left (CannotElaborate position "Data-case constructor comparison budget exhausted")
          _ => Left (CannotElaborate position "Data-case constructor does not match the scrutinee type and shape")
      go _ _ _ _ = Left (CannotElaborate position "Data-case constructor payload arity does not match its branch")

  ||| Motive for one pair level: the dependent body when known, else a constant
  ||| result lifted out of the two binders this level introduced.
  pairLevelMotive : Position -> Term m -> Maybe (Term (S m)) -> Maybe (Term (S (S m))) -> Either ResolveError (Term m, Maybe (Term m))
  pairLevelMotive position tailTy (Just body) _ = Right (Lambda Erased tailTy body, Nothing)
  pairLevelMotive position tailTy Nothing (Just inner) = case dropNewest inner >>= dropNewest of
    Just outer => Right (Lambda Erased tailTy (weaken outer), Just outer)
    Nothing => Left (CannotElaborate position "Data-case result depends on a constructor field; use an explicit return motive")
  pairLevelMotive position tailTy Nothing Nothing = Left (CannotElaborate position "Cannot infer data-case result; use an explicit return motive")

  ||| Bind the fields of a multi-field constructor payload. The payload is a
  ||| right-nested pair, so each level is one `PairCase` on the newest variable
  ||| (the payload, then each linear tail). `motiveBody` is the dependent result
  ||| type in terms of that variable (absent when no motive is known, in which case
  ||| a constant result is inferred from the body). Also returns the inferred
  ||| constant result at this level. `named` is a named catch-all: its token and the
  ||| rebuilt constructor value, in terms of the same variable as `motiveBody`; the body
  ||| sees that value through an unrestricted binding, so it needs unrestricted fields.
  ||| The core checker validates the whole term.
  multiFieldLevel : GlobalContext -> List GlobalDefinition -> Position -> Context m -> Vect m String -> Term m -> Term m -> List Token ->
                    Maybe (Term (S m)) -> Maybe (Token, Term (S m)) -> Expr -> Either ResolveError (Term m, Maybe (Term m))
  multiFieldLevel shared globals position ctx env scrutinee tailTy [first, second] motiveBody named body = case tailTy of
    Sigma q r domain rest => do
      let inner = Extend (Extend ctx q domain) r rest
      let scope = second.spelling :: first.spelling :: env
      let packed = PairValue (rename (FS . FS) tailTy) (Variable (FS FZ)) (Variable FZ)
      let replace : Fin (S m) -> Term (S (S m))
          replace FZ = packed
          replace (FS i) = Variable (FS (FS i))
      let expectedBody = map (\result => let applied = substituteTerm replace result in
                                          fromMaybe applied (guardedNormalGlobals shared typeReductionFuel applied)) motiveBody
      checked <- case named of
        Nothing => case expectedBody of
          Just expected => elaborateExpectedGlobals shared globals inner scope expected body
          Nothing => elaborateInWithGlobals shared globals (Just inner) scope body
        Just (name, value) => case substituteTerm replace value of
          rebuilt@(NominalValue valueType _) => do
            let withValue = Extend inner Unrestricted valueType
            result <- case expectedBody of
              Just expected => elaborateExpectedGlobals shared globals withValue (name.spelling :: scope) (weaken expected) body
              Nothing => elaborateInWithGlobals shared globals (Just withValue) (name.spelling :: scope) body
            Right (Apply (Lambda Unrestricted valueType result) rebuilt)
          _ => Left (CannotElaborate position "Invalid data-case catch-all value")
      inferred <- case motiveBody of
        Just _ => Right Nothing
        Nothing => case inferErasedGlobals shared checkingDepth typeReductionFuel inner checked of
          Left err => Left (CannotElaborate position ("Cannot infer data-case branch type: " ++ show err ++ "; use an explicit return motive"))
          Right ty => Right (Just ty)
      (motive, result) <- pairLevelMotive position tailTy motiveBody inferred
      Right (PairCase motive scrutinee (Lambda q domain (Lambda r rest checked)), result)
    _ => Left (CannotElaborate position "Data-case constructor payload arity does not match its branch")
  multiFieldLevel shared globals position ctx env scrutinee tailTy (first :: rest@(_ :: _ :: _)) motiveBody named body = case tailTy of
    Sigma q r domain remaining => do
      let inner = Extend (Extend ctx q domain) r remaining
      let scope = "$field.tail" :: first.spelling :: env
      let packed = PairValue (rename (FS . FS . FS) tailTy) (Variable (FS (FS FZ))) (Variable FZ)
      let replace : Fin (S m) -> Term (S (S (S m)))
          replace FZ = packed
          replace (FS i) = Variable (FS (FS (FS i)))
      (nested, nestedResult) <- multiFieldLevel shared globals position inner scope (Variable FZ) (weaken remaining) rest
                                  (map (substituteTerm replace) motiveBody)
                                  (map (\(name, value) => (name, substituteTerm replace value)) named) body
      (motive, result) <- pairLevelMotive position tailTy motiveBody nestedResult
      Right (PairCase motive scrutinee (Lambda q domain (Lambda r remaining nested)), result)
    _ => Left (CannotElaborate position "Data-case constructor payload arity does not match its branch")
  multiFieldLevel shared globals position ctx env scrutinee tailTy _ motiveBody named body =
    Left (CannotElaborate position "Data-case constructor payload arity does not match its branch")

  orderDataArms : Position -> Nat -> List (Maybe (Quantity, Term n)) -> List (Nat, Term n) -> Either ResolveError (List (Term n))
  orderDataArms position tag [] [] = Right []
  orderDataArms position tag [] _ = Left (CannotElaborate position "Unexpected data-case branch")
  orderDataArms position tag (_ :: rest) branches = do
    branch <- case lookup tag branches of Nothing => Left (CannotElaborate position "Missing data-case constructor"); Just body => Right body
    later <- orderDataArms position (S tag) rest (filter (\entry => fst entry /= tag) branches)
    Right (branch :: later)

  elaborateDataArmsGlobals : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> Term n -> Term n -> List (Term n) ->
                      List (Maybe (Quantity, Term n)) -> Maybe (Term n) -> List Token -> List (Token, List Token, Expr) -> Either ResolveError (List (Nat, Term n))
  elaborateDataArmsGlobals shared globals ctx env nominal shape indices descriptors hint clauseNames [] = Right []
  elaborateDataArmsGlobals shared globals ctx env nominal shape indices descriptors hint clauseNames ((name, binder, body) :: rest) =
    if null rest && not (null clauseNames) && null binder && isCatchAllHead globals env name
      then do
        covered <- coveredTagsGlobals shared globals env indices (reverse (drop 1 (reverse clauseNames)))
        if length (nub covered) >= length descriptors
          then Left (CannotElaborate name.span.start "Catch-all clause is unreachable: every constructor is already matched")
          else catchAllArmsGlobals shared globals ctx env nominal shape hint name body covered 0 descriptors
      else do
        if elem '.' (unpack name.spelling) then Right () else
          case lookupName name.spelling env of
            Just _ => Left (CannotElaborate name.span.start "Data-case constructor is shadowed by a local binder")
            Nothing => Right ()
        definition <- case find (\entry => entry.name == name.spelling) globals of
          Nothing => case qualifiedCandidates name.spelling globals of
            candidates@(_ :: _ :: _) => Left (CannotElaborate name.span.start (ambiguityMessage name.spelling candidates))
            _ => Left (Unbound name.span.start name.spelling)
          Just entry => Right entry
        if definition.quantity /= Unrestricted then Left (CannotElaborate name.span.start "Data-case constructor must be an unrestricted checked global") else Right ()
        if coreNodes definition.value > 512 then Left (CannotElaborate name.span.start "Data-case constructor exceeds 512 nodes") else Right ()
        let candidate = foldl Apply (rename absurd definition.value) indices
        tag <- dataCaseTagGlobals shared name.span.start candidate
        descriptor <- case variantAt tag descriptors of
          Nothing => Left (CannotElaborate name.span.start "Data-case constructor tag is outside the scrutinee shape")
          Just descriptor => Right descriptor
        arity <- case normalizeGlobals (globalValue shared) typeReductionFuel candidate of
          OutOfFuel _ => Left (CannotElaborate name.span.start "Data-case constructor reduction budget exhausted")
          Normal normal => Right (constructorFieldCount normal)
        if arity /= length binder
          then Left (CannotElaborate name.span.start ("Data-case constructor " ++ name.spelling ++ " has " ++ show arity ++
                     " field(s) but the pattern binds " ++ show (length binder)))
          else Right ()
        case binder of
          _ :: _ :: _ => do
            _ <- multiFieldConstructorTag shared name.span.start (length binder) nominal shape candidate
            Right ()
          _ => do
            expected <- case (descriptor, binder) of
              (Nothing, []) => Right (NominalValue nominal (VariantValue shape tag Nothing))
              (Just (q, ty), [_]) =>
                Right (Lambda q ty (NominalValue (weaken nominal) (VariantValue (weaken shape) tag (Just (Variable FZ)))))
              _ => Left (CannotElaborate name.span.start "Data-case constructor payload arity does not match its branch")
            case betaCompareGlobals (globalValue shared) typeReductionFuel candidate expected of
              EqualNormalForms => Right ()
              DifferentNormalForms => Left (CannotElaborate name.span.start "Data-case constructor does not match the scrutinee type and shape")
              Inconclusive => Left (CannotElaborate name.span.start "Data-case constructor comparison budget exhausted")
        branch <- case (descriptor, binder) of
          (Nothing, []) => case hint of
            Nothing => elaborateInWithGlobals shared globals (Just ctx) env body
            Just motive =>
              let applied = Apply motive (NominalValue nominal (VariantValue shape tag Nothing))
                  result = fromMaybe applied (guardedNormalGlobals shared typeReductionFuel applied) in
                elaborateExpectedGlobals shared globals ctx env result body
          (Just (q, ty), [bound]) => do
            result <- case hint of
              Nothing => elaborateInWithGlobals shared globals (Just (Extend ctx q ty)) (bound.spelling :: env) body
              Just motive =>
                let value = NominalValue (weaken nominal) (VariantValue (weaken shape) tag (Just (Variable FZ)))
                    applied = Apply (weaken motive) value
                    expectedResult = fromMaybe applied (guardedNormalGlobals shared typeReductionFuel applied) in
                  elaborateExpectedGlobals shared globals (Extend ctx q ty) (bound.spelling :: env) expectedResult body
            Right (Lambda q ty result)
          (Just (q, ty), first :: second :: more) => do
            -- Same shape as `assemblePairPayloadBranch`, nested once per extra field.
            let motiveBody = map (\motive => Apply (rename (FS . FS) motive)
                  (NominalValue (rename (FS . FS) nominal) (VariantValue (rename (FS . FS) shape) tag (Just (Variable FZ))))) hint
            (level, _) <- multiFieldLevel shared globals name.span.start (Extend ctx q ty) ("$payload" :: env) (Variable FZ) (weaken ty)
                            (first :: second :: more) motiveBody Nothing body
            Right (Lambda q ty level)
          _ => Left (CannotElaborate name.span.start "Invalid data-case payload branch")
        following <- elaborateDataArmsGlobals shared globals ctx env nominal shape indices descriptors hint clauseNames rest
        if any (\entry => fst entry == tag) following
           then Left (CannotElaborate name.span.start "Duplicate data-case constructor") else Right ()
        Right ((tag, branch) :: following)

  ||| Tags of the constructors named by earlier clauses, resolved like
  ||| `elaborateDataArmsGlobals` but without elaborating any body.
  coveredTagsGlobals : GlobalContext -> List GlobalDefinition -> Vect n String -> List (Term n) -> List Token -> Either ResolveError (List Nat)
  coveredTagsGlobals shared globals env indices [] = Right []
  coveredTagsGlobals shared globals env indices (name :: rest) = do
    definition <- case find (\entry => entry.name == name.spelling) globals of
      Nothing => case qualifiedCandidates name.spelling globals of
        candidates@(_ :: _ :: _) => Left (CannotElaborate name.span.start (ambiguityMessage name.spelling candidates))
        _ => Left (Unbound name.span.start name.spelling)
      Just entry => Right entry
    tag <- dataCaseTagGlobals shared name.span.start (foldl Apply (rename absurd definition.value) indices)
    later <- coveredTagsGlobals shared globals env indices rest
    Right (tag :: later)

  ||| One omitted constructor of a clause-group catch-all. `_` drops the value (a
  ||| linear payload then fails the ordinary usage check); a name rebinds the
  ||| reconstructed value through an unrestricted let, so it needs an
  ||| unrestricted payload. The unchanged core checker enforces both.
  catchAllArmGlobals : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> Term n -> Term n -> Maybe (Term n) ->
                       Token -> Expr -> Nat -> Maybe (Quantity, Term n) -> Either ResolveError (Nat, Term n)
  catchAllArmGlobals shared globals ctx env nominal shape hint head body tag Nothing = do
    let value = NominalValue nominal (VariantValue shape tag Nothing)
    let expectedResult = map (\motive => let applied = Apply motive value in fromMaybe applied (guardedNormalGlobals shared typeReductionFuel applied)) hint
    if head.spelling == "_"
      then do
        result <- case expectedResult of
          Nothing => elaborateInWithGlobals shared globals (Just ctx) env body
          Just expected => elaborateExpectedGlobals shared globals ctx env expected body
        Right (tag, result)
      else do
        let inner = Extend ctx Unrestricted nominal
        result <- case expectedResult of
          Nothing => elaborateInWithGlobals shared globals (Just inner) (head.spelling :: env) body
          Just expected => elaborateExpectedGlobals shared globals inner (head.spelling :: env) (weaken expected) body
        Right (tag, Apply (Lambda Unrestricted nominal result) value)
  catchAllArmGlobals shared globals ctx env nominal shape hint head body tag (Just (q, ty)) =
    -- A catch-all over a multi-field payload destructures it with ignored binders:
    -- `_` drops the fields, a name rebuilds the value from them. Either way every
    -- field must be unrestricted or erased; the core checker enforces that.
    if q == Linear && payloadFieldCount ty >= 2
      then do
        let wide = rename (FS . FS)
        let value = NominalValue (wide nominal) (VariantValue (wide shape) tag (Just (Variable FZ)))
        let motiveBody = map (\motive => Apply (wide motive) value) hint
        let dropped = { spelling := "_" } head
        (level, _) <- multiFieldLevel shared globals head.span.start (Extend ctx q ty) ("$payload" :: env) (Variable FZ) (weaken ty)
                        (replicate (payloadFieldCount ty) dropped) motiveBody
                        (if head.spelling == "_" then Nothing else Just (head, value)) body
        Right (tag, Lambda q ty level)
      else catchAllUnaryPayloadArm shared globals ctx env nominal shape hint head body tag q ty
  catchAllUnaryPayloadArm : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> Term n -> Term n -> Maybe (Term n) ->
                            Token -> Expr -> Nat -> Quantity -> Term n -> Either ResolveError (Nat, Term n)
  catchAllUnaryPayloadArm shared globals ctx env nominal shape hint head body tag q ty = do
    let value = NominalValue (weaken nominal) (VariantValue (weaken shape) tag (Just (Variable FZ)))
    let expectedResult = map (\motive => let applied = Apply (weaken motive) value in fromMaybe applied (guardedNormalGlobals shared typeReductionFuel applied)) hint
    let payloadContext = Extend ctx q ty
    let payloadEnv = "$catchall.payload" :: env
    if head.spelling == "_"
      then do
        result <- case expectedResult of
          Nothing => elaborateInWithGlobals shared globals (Just payloadContext) payloadEnv body
          Just expected => elaborateExpectedGlobals shared globals payloadContext payloadEnv expected body
        Right (tag, Lambda q ty result)
      else do
        let inner = Extend payloadContext Unrestricted (weaken nominal)
        result <- case expectedResult of
          Nothing => elaborateInWithGlobals shared globals (Just inner) (head.spelling :: payloadEnv) body
          Just expected => elaborateExpectedGlobals shared globals inner (head.spelling :: payloadEnv) (weaken expected) body
        Right (tag, Lambda q ty (Apply (Lambda Unrestricted (weaken nominal) result) value))

  ||| Expand the catch-all over every constructor tag not in `covered`.
  catchAllArmsGlobals : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> Term n -> Term n -> Maybe (Term n) ->
                        Token -> Expr -> List Nat -> Nat -> List (Maybe (Quantity, Term n)) -> Either ResolveError (List (Nat, Term n))
  catchAllArmsGlobals shared globals ctx env nominal shape hint head body covered tag [] = Right []
  catchAllArmsGlobals shared globals ctx env nominal shape hint head body covered tag (descriptor :: rest) = do
    later <- catchAllArmsGlobals shared globals ctx env nominal shape hint head body covered (S tag) rest
    if elem tag covered then Right later else do
      arm <- catchAllArmGlobals shared globals ctx env nominal shape hint head body tag descriptor
      Right (arm :: later)

  ||| A final clause head is a catch-all when it is `_` or an unresolved
  ||| lowercase name; resolvable names stay constructors.
  isCatchAllHead : List GlobalDefinition -> Vect n String -> Token -> Bool
  isCatchAllHead globals env token = token.spelling == "_" ||
    ((case unpack token.spelling of c :: _ => isLower c; [] => False) &&
     isNothing (lookupName token.spelling env) &&
     isNothing (find (\entry => entry.name == token.spelling) globals) &&
     null (qualifiedCandidates token.spelling globals))

  ||| Unary recursive and sequence data have exactly two constructors (tags 0 and
  ||| 1). A final catch-all clause stands for the one the earlier clauses did not
  ||| name; the arm then binds `_` payloads, so a linear payload is rejected.
  catchAllTag : List GlobalDefinition -> Token -> List Token -> (GlobalDefinition -> Either ResolveError Nat) -> Either ResolveError Nat
  catchAllTag globals head earlier classify = do
    covered <- traverse (\named => case find (\entry => entry.name == named.spelling) globals of
                                    Nothing => Left (Unbound named.span.start named.spelling)
                                    Just entry => classify entry) earlier
    case Prelude.List.filter (\tag => not (elem tag covered)) [0, 1] of
      [] => Left (CannotElaborate head.span.start "Catch-all clause is unreachable: every constructor is already matched")
      missing :: _ => Right missing

  -- A result type is available here only for a direct equation body. The
  -- variable abstraction is a renaming, so it cannot duplicate subtrees.
  public export
  elaborateExpectedGlobals : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> Term n -> Expr -> Either ResolveError (Term n)
  elaborateExpectedGlobals shared globals context env expected reference@(NRef span name) =
    if scopeProbe name && isNothing (lookupName name env) && isNothing (lookupGlobal name globals) then Left (scopeFailure shared globals (Just context) env (Just expected) span.start name)
      else elaborateInWithGlobals shared globals (Just context) env reference
  elaborateExpectedGlobals shared globals context env expected expression@(NApply span function argument) =
    if hasImplicitCall globals env expression
      then elaborateImplicitCallGlobals shared globals context env (Just expected) expression
      else do
        resolved <- elaborateInWithGlobals shared globals (Just context) env function
        elaborateApplicationGlobals shared globals (Just context) env resolved argument
  elaborateExpectedGlobals shared globals context env expected expression@(NImplicitApply span _ _) =
    elaborateImplicitCallGlobals shared globals context env (Just expected) expression
  elaborateExpectedGlobals shared globals context env expected (NDataCase span value Nothing arms) =
    elaborateDataCaseGlobals shared globals context env span value Nothing arms (Just expected)
  elaborateExpectedGlobals shared globals context env expected (NCaseEither span asRecord asData) =
    case elaborateExpectedGlobals shared globals context env expected asRecord of
      Right term => Right term
      Left failure => case elaborateExpectedGlobals shared globals context env expected asData of
        Right term => Right term
        Left other => if isJust other.completion then Left other else Left failure
  elaborateExpectedGlobals shared globals context env (Pi _ _ expected) (NLambda span q name domain body) = do
    authored <- elaborateInWithGlobals shared globals (Just context) env domain
    let domain = fromMaybe authored (familyAnnotation shared authored)
    body <- elaborateExpectedGlobals shared globals (Extend context q domain) (name :: env) expected body
    Right (Lambda q domain body)
  elaborateExpectedGlobals shared globals context env expected (NUnitCase span scrutinee body) = do
    scrutinee <- elaborateInWithGlobals shared globals (Just context) env scrutinee
    body <- elaborateExpectedGlobals shared globals context env expected body
    Right (UnitCase scrutinee body)
  elaborateExpectedGlobals shared globals context env expected (NIf span condition yes no) = do
    condition <- elaborateInWithGlobals shared globals (Just context) env condition
    yes <- elaborateExpectedGlobals shared globals context env expected yes
    no <- elaborateExpectedGlobals shared globals context env expected no
    Right (BoolCase condition yes no)
  elaborateExpectedGlobals shared globals context env expected expression@(NLet span q name annotation value body) =
    if not (wantsExpected body || hasImplicitCall globals (name :: env) body) || typeNodes expected > inferredResultNodes
      then elaborateInWithGlobals shared globals (Just context) env expression else do
      ty <- elaborateInWithGlobals shared globals (Just context) env annotation
      value <- elaborateExpectedGlobals shared globals context env ty value
      body <- elaborateExpectedGlobals shared globals (Extend context q ty) (name :: env) (weaken expected) body
      Right (Apply (Lambda q ty body) value)
  elaborateExpectedGlobals shared globals context env expected body = elaborateInWithGlobals shared globals (Just context) env body

  -- Try the authored scrutinee first to preserve exact-abstraction behavior.
  -- Only a fully admitted guarded normalization may supply a second proposal;
  -- both candidates are checked against the original, unnormalized result.
  chooseExpectedMotiveGlobals : GlobalContext -> Position -> Context n -> Term n -> Term n -> Term n -> Term n -> List (Term n) -> Either ResolveError (Term n)
  chooseExpectedMotiveGlobals shared position ctx nominal shape scrutinee result branches = do
    exact <- expectedDataMotive position nominal result scrutinee
    let candidate = assembleDataCase nominal shape exact scrutinee branches
    case checkErasedGlobals shared checkingDepth typeReductionFuel ctx candidate result of
      Right () => Right exact
      Left _ => case guardedNormalGlobals shared typeReductionFuel scrutinee of
        Nothing => Right exact
        Just normal => if sameSyntax normal scrutinee then Right exact else
          case expectedDataMotive position nominal result normal of
            Left _ => Right exact
            Right converted =>
              let alternative = assembleDataCase nominal shape converted scrutinee branches in
                case checkErasedGlobals shared checkingDepth typeReductionFuel ctx alternative result of
                  Right () => Right converted
                  Left _ => Right exact

  -- Identify constructors from their checked closed values, never from the
  -- authored layout hint. Guard conversion before allocating normalized terms.
  recursiveCaseArmsGlobals : GlobalContext -> Position -> List GlobalDefinition -> Context n -> Vect n String -> Term n -> Maybe (Term n) -> List Token -> List (Token, List Token, Expr) -> Either ResolveError (List (Nat, Term n))
  recursiveCaseArmsGlobals shared position globals ctx env ty hint clauseNames [] = Right []
  recursiveCaseArmsGlobals shared position globals ctx env ty@(RecType key) hint clauseNames ((name, binder, body) :: rest) = do
    let catchAll = null rest && not (null clauseNames) && null binder && isCatchAllHead globals env name
    let terminal : Term 0 = RecEnd (RecType key)
    let successor : Term 0 = Lambda Linear (RecType key) (RecMore (RecType key) (Variable FZ))
    tag <- the (Either ResolveError Nat) $ if catchAll
      then catchAllTag globals name (reverse (drop 1 (reverse clauseNames))) (\definition =>
        case guardedNormalGlobals shared typeReductionFuel definition.value of
          Nothing => Left (CannotElaborate name.span.start "Recursive-case constructor comparison exhausted admission or reduction")
          Just normal => if sameSyntax normal terminal then Right 0 else if sameSyntax normal successor then Right 1
            else Left (CannotElaborate name.span.start "Recursive-case constructor does not match the scrutinee family"))
      else do
      if elem '.' (unpack name.spelling) then Right () else case lookupName name.spelling env of
        Just _ => Left (CannotElaborate name.span.start "Data-case constructor is shadowed by a local binder")
        Nothing => Right ()
      definition <- case find (\entry => entry.name == name.spelling) globals of
        Nothing => case qualifiedCandidates name.spelling globals of
          _ :: _ :: _ => Left (CannotElaborate name.span.start ("Ambiguous imported name " ++ name.spelling ++ "; use a qualified name"))
          _ => Left (Unbound name.span.start name.spelling)
        Just entry => Right entry
      if definition.quantity /= Unrestricted then Left (CannotElaborate name.span.start "Data-case constructor must be an unrestricted checked global") else Right ()
      normal <- case guardedNormalGlobals shared typeReductionFuel definition.value of
        Nothing => Left (CannotElaborate name.span.start "Recursive-case constructor comparison exhausted admission or reduction")
        Just result => Right result
      if sameSyntax normal terminal then Right 0 else
        if sameSyntax normal successor then Right 1 else
          Left (CannotElaborate name.span.start "Recursive-case constructor does not match the scrutinee family")
    let blank : Token = { spelling := "_" } name
    let payload : List Token = if catchAll && tag == 1 then [blank] else binder
    branch <- case (tag, payload) of
      (0, []) => case hint of
        Nothing => elaborateInWithGlobals shared globals (Just ctx) env body
        Just motive =>
          let applied = Apply motive (RecEnd ty)
              result = fromMaybe applied (guardedNormalGlobals shared typeReductionFuel applied) in
            elaborateExpectedGlobals shared globals ctx env result body
      (1, [bound]) => do
        result <- case hint of
          Nothing => elaborateInWithGlobals shared globals (Just (Extend ctx Linear ty)) (bound.spelling :: env) body
          Just motive =>
            let actual = RecMore (weaken ty) (Variable FZ)
                applied = Apply (weaken motive) actual
                expectedResult = fromMaybe applied (guardedNormalGlobals shared typeReductionFuel applied) in
              elaborateExpectedGlobals shared globals (Extend ctx Linear ty) (bound.spelling :: env) expectedResult body
        Right (Lambda Linear ty result)
      _ => Left (CannotElaborate name.span.start "Recursive-case constructor payload arity does not match its branch")
    following <- recursiveCaseArmsGlobals shared position globals ctx env ty hint clauseNames rest
    if any (\entry => fst entry == tag) following
      then Left (CannotElaborate name.span.start "Duplicate recursive-case constructor") else Right ()
    Right ((tag, branch) :: following)
  recursiveCaseArmsGlobals shared position _ _ _ _ _ _ _ = Left (CannotElaborate position "Invalid recursive-case type")

  chooseExpectedRecursiveMotiveGlobals : GlobalContext -> Position -> Context n -> Term n -> Term n -> Term n -> Term n -> Term n -> Either ResolveError (Term n)
  chooseExpectedRecursiveMotiveGlobals shared position ctx ty scrutinee result base more = do
    exact <- expectedDataMotive position ty result scrutinee
    case checkErasedGlobals shared checkingDepth typeReductionFuel ctx (RecCase exact scrutinee base more) result of
      Right () => Right exact
      Left _ => case guardedNormalGlobals shared typeReductionFuel scrutinee of
        Nothing => Left (CannotElaborate position "Cannot infer recursive-case motive; use an explicit return motive")
        Just normal => if sameSyntax normal scrutinee
          then Left (CannotElaborate position "Cannot infer recursive-case motive; use an explicit return motive")
          else do
            converted <- expectedDataMotive position ty result normal
            case checkErasedGlobals shared checkingDepth typeReductionFuel ctx (RecCase converted scrutinee base more) result of
              Right () => Right converted
              Left _ => Left (CannotElaborate position "Cannot infer recursive-case motive; use an explicit return motive")

  elaborateRecursiveDataCaseGlobals : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> SourceSpan -> Term n -> Term n -> Maybe Expr -> List (Token, List Token, Expr) -> Maybe (Term n) -> Either ResolveError (Term n)
  elaborateRecursiveDataCaseGlobals shared globals ctx env span scrutinee ty motive arms expected = do
    if typeNodes ty > inferredResultNodes || payloadSize ty > payloadLimit
      then Left (CannotElaborate span.start "Recursive-case type exceeds admission") else Right ()
    if length arms > 64 then Left (CannotElaborate span.start "Data-case branch admission exhausted (64)") else Right ()
    explicit <- the (Either ResolveError (Maybe (Term n))) $ case motive of
      Just authored => Just <$> elaborateInWithGlobals shared globals (Just ctx) env authored
      Nothing => Right Nothing
    let hint : Maybe (Term n)
        hint = case explicit of
          Just authored => Just authored
          Nothing => case expected of
            Just result => case expectedDataMotive span.start ty result scrutinee of
              Right candidate => Just candidate
              Left _ => Nothing
            Nothing => Nothing
    let boundedHint = case hint of
          Just candidate => if typeNodes candidate <= inferredResultNodes && payloadSize candidate <= payloadLimit then Just candidate else Nothing
          Nothing => Nothing
    let catchAll = case scrutinee of
          Variable i => index i env == "$clauseScrutinee"
          _ => False
    let clauseNames = if catchAll then map (\arm => fst arm) arms else []
    checked <- recursiveCaseArmsGlobals shared span.start globals ctx env ty boundedHint clauseNames arms
    ordered <- orderDataArms span.start 0 [Nothing, Just (Linear, ty)] checked
    case ordered of
      [base, more] => do
        selected <- case explicit of
          Just authored => Right authored
          Nothing => case expected of
            Just result => case constantDataResultGlobals shared span.start ctx [Nothing, Just (Linear, ty)] ordered of
              Right common =>
                let constant = Lambda Erased ty (weaken common) in
                  case checkErasedGlobals shared checkingDepth typeReductionFuel ctx (RecCase constant scrutinee base more) result of
                    Right () => Right constant
                    Left _ => chooseExpectedRecursiveMotiveGlobals shared span.start ctx ty scrutinee result base more
              Left _ => chooseExpectedRecursiveMotiveGlobals shared span.start ctx ty scrutinee result base more
            Nothing => do
              result <- constantDataResultGlobals shared span.start ctx [Nothing, Just (Linear, ty)] ordered
              Right (Lambda Erased ty (weaken result))
        Right (RecCase selected scrutinee base more)
      _ => Left (CannotElaborate span.start "Recursive case requires exactly two branches")

  natCaseArmsGlobals : GlobalContext -> Position -> Quantity -> List GlobalDefinition -> Context n -> Vect n String -> Term n -> Maybe (Term n) -> List (Token, List Token, Expr) -> Either ResolveError (List (Nat, Term n))
  natCaseArmsGlobals shared position predQ globals ctx env ty hint [] = Right []
  natCaseArmsGlobals shared position predQ globals ctx env ty@NatType hint ((name, binder, body) :: rest) = do
    if elem '.' (unpack name.spelling) then Right () else case lookupName name.spelling env of
      Just _ => Left (CannotElaborate name.span.start "Data-case constructor is shadowed by a local binder")
      Nothing => Right ()
    definition <- case find (\entry => entry.name == name.spelling) globals of
      Nothing => case qualifiedCandidates name.spelling globals of
        _ :: _ :: _ => Left (CannotElaborate name.span.start ("Ambiguous imported name " ++ name.spelling ++ "; use a qualified name"))
        _ => Left (Unbound name.span.start name.spelling)
      Just entry => Right entry
    if definition.quantity /= Unrestricted then Left (CannotElaborate name.span.start "Data-case constructor must be an unrestricted checked global") else Right ()
    normal <- case guardedNormalGlobals shared typeReductionFuel definition.value of
      Nothing => Left (CannotElaborate name.span.start "Nat-case constructor comparison exhausted admission or reduction")
      Just result => Right result
    let terminal : Term 0 = NatZero
    let successor : Term 0 = Lambda Linear NatType (NatSucc (Variable FZ))
    tag <- if sameSyntax normal terminal then Right 0 else
             if sameSyntax normal successor then Right 1 else
               Left (CannotElaborate name.span.start "Nat-case constructor does not match the scrutinee family")
    branch <- case (tag, binder) of
      (0, []) => case hint of
        Nothing => elaborateInWithGlobals shared globals (Just ctx) env body
        Just motive =>
          let applied = Apply motive (NatZero)
              result = fromMaybe applied (guardedNormalGlobals shared typeReductionFuel applied) in
            elaborateExpectedGlobals shared globals ctx env result body
      (1, [bound]) => do
        result <- case hint of
          Nothing => elaborateInWithGlobals shared globals (Just (Extend ctx predQ ty)) (bound.spelling :: env) body
          Just motive =>
            let actual = NatSucc (Variable FZ)
                applied = Apply (weaken motive) actual
                expectedResult = fromMaybe applied (guardedNormalGlobals shared typeReductionFuel applied) in
              elaborateExpectedGlobals shared globals (Extend ctx predQ ty) (bound.spelling :: env) expectedResult body
        Right (Lambda predQ ty result)
      _ => Left (CannotElaborate name.span.start "Nat-case constructor payload arity does not match its branch")
    following <- natCaseArmsGlobals shared position predQ globals ctx env ty hint rest
    if any (\entry => fst entry == tag) following
      then Left (CannotElaborate name.span.start "Duplicate Nat-case constructor") else Right ()
    Right ((tag, branch) :: following)
  natCaseArmsGlobals shared position _ _ _ _ _ _ _ = Left (CannotElaborate position "Invalid Nat-case type")

  chooseExpectedNatMotiveGlobals : GlobalContext -> Position -> Context n -> Term n -> Term n -> Term n -> Term n -> Term n -> Either ResolveError (Term n)
  chooseExpectedNatMotiveGlobals shared position ctx ty scrutinee result base more = do
    exact <- expectedDataMotive position ty result scrutinee
    case checkErasedGlobals shared checkingDepth typeReductionFuel ctx (NatCase exact scrutinee base more) result of
      Right () => Right exact
      Left _ => case guardedNormalGlobals shared typeReductionFuel scrutinee of
        Nothing => Left (CannotElaborate position "Cannot infer Nat-case motive; use an explicit return motive")
        Just normal => if sameSyntax normal scrutinee
          then Left (CannotElaborate position "Cannot infer Nat-case motive; use an explicit return motive")
          else do
            converted <- expectedDataMotive position ty result normal
            case checkErasedGlobals shared checkingDepth typeReductionFuel ctx (NatCase converted scrutinee base more) result of
              Right () => Right converted
              Left _ => Left (CannotElaborate position "Cannot infer Nat-case motive; use an explicit return motive")

  elaborateNatDataCaseGlobals : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> SourceSpan -> Term n -> Term n -> Maybe Expr -> List (Token, List Token, Expr) -> Maybe (Term n) -> Either ResolveError (Term n)
  elaborateNatDataCaseGlobals shared globals ctx env span scrutinee ty motive arms expected = do
    if typeNodes ty > inferredResultNodes || payloadSize ty > payloadLimit
      then Left (CannotElaborate span.start "Nat-case type exceeds admission") else Right ()
    if length arms > 64 then Left (CannotElaborate span.start "Data-case branch admission exhausted (64)") else Right ()
    explicit <- the (Either ResolveError (Maybe (Term n))) $ case motive of
      Just authored => Just <$> elaborateInWithGlobals shared globals (Just ctx) env authored
      Nothing => Right Nothing
    let hint : Maybe (Term n)
        hint = case explicit of
          Just authored => Just authored
          Nothing => case expected of
            Just result => case expectedDataMotive span.start ty result scrutinee of
              Right candidate => Just candidate
              Left _ => Nothing
            Nothing => Nothing
    let boundedHint = case hint of
          Just candidate => if typeNodes candidate <= inferredResultNodes && payloadSize candidate <= payloadLimit then Just candidate else Nothing
          Nothing => Nothing
    checked <- natCaseArmsGlobals shared span.start (predecessorQuantity ctx env scrutinee) globals ctx env ty boundedHint arms
    ordered <- orderDataArms span.start 0 [Nothing, Just (Linear, ty)] checked
    case ordered of
      [base, more] => do
        selected <- case explicit of
          Just authored => Right authored
          Nothing => case expected of
            Just result => case constantDataResultGlobals shared span.start ctx [Nothing, Just (Linear, ty)] ordered of
              Right common =>
                let constant = Lambda Erased ty (weaken common) in
                  case checkErasedGlobals shared checkingDepth typeReductionFuel ctx (NatCase constant scrutinee base more) result of
                    Right () => Right constant
                    Left _ => chooseExpectedNatMotiveGlobals shared span.start ctx ty scrutinee result base more
              Left _ => chooseExpectedNatMotiveGlobals shared span.start ctx ty scrutinee result base more
            Nothing => do
              result <- constantDataResultGlobals shared span.start ctx [Nothing, Just (Linear, ty)] ordered
              Right (Lambda Erased ty (weaken result))
        Right (NatCase selected scrutinee base more)
      _ => Left (CannotElaborate span.start "Nat case requires exactly two branches")

  sequenceCaseArmsGlobals : GlobalContext -> Position -> List GlobalDefinition -> Context n -> Vect n String -> Term n -> Term n -> Maybe (Term n) -> List Token -> List (Token, List Token, Expr) -> Either ResolveError (List (Nat, Term n))
  sequenceCaseArmsGlobals shared position globals ctx env ty element hint clauseNames [] = Right []
  sequenceCaseArmsGlobals shared position globals ctx env ty element hint clauseNames ((name, binders, body) :: rest) = do
    let catchAll = null rest && not (null clauseNames) && null binders && isCatchAllHead globals env name
    tag <- the (Either ResolveError Nat) $ if catchAll
      then catchAllTag globals name (reverse (drop 1 (reverse clauseNames))) (checkedSequenceConstructorGlobals shared name.span.start ctx ty element)
      else do
      if elem '.' (unpack name.spelling) then Right () else case lookupName name.spelling env of
        Just _ => Left (CannotElaborate name.span.start "Data-case constructor is shadowed by a local binder")
        Nothing => Right ()
      definition <- case find (\entry => entry.name == name.spelling) globals of
        Nothing => case qualifiedCandidates name.spelling globals of
          _ :: _ :: _ => Left (CannotElaborate name.span.start ("Ambiguous imported name " ++ name.spelling ++ "; use a qualified name"))
          _ => Left (Unbound name.span.start name.spelling)
        Just entry => Right entry
      checkedSequenceConstructorGlobals shared name.span.start ctx ty element definition
    let blank : Token = { spelling := "_" } name
    let payload : List Token = if catchAll && tag == 1 then [blank, blank] else binders
    let nil = SeqNil ty
    branch <- case (tag, payload) of
      (0, []) => case hint of
        Nothing => elaborateInWithGlobals shared globals (Just ctx) env body
        Just motive =>
          let applied = Apply motive nil
              result = fromMaybe applied (guardedNormalGlobals shared typeReductionFuel applied) in
            elaborateExpectedGlobals shared globals ctx env result body
      (1, [head, tail]) => do
        let inner = Extend (Extend ctx Linear element) Linear (weaken ty)
        result <- case hint of
          Nothing => elaborateInWithGlobals shared globals (Just inner) (tail.spelling :: head.spelling :: env) body
          Just motive =>
            let actual = SeqCons (weaken (weaken ty)) (Variable (FS FZ)) (Variable FZ)
                applied = Apply (weaken (weaken motive)) actual
                expectedResult = fromMaybe applied (guardedNormalGlobals shared typeReductionFuel applied) in
              elaborateExpectedGlobals shared globals inner (tail.spelling :: head.spelling :: env) expectedResult body
        Right (Lambda Linear element (Lambda Linear (weaken ty) result))
      _ => Left (CannotElaborate name.span.start "Sequence-case constructor payload arity does not match its branch")
    following <- sequenceCaseArmsGlobals shared position globals ctx env ty element hint clauseNames rest
    if any (\entry => fst entry == tag) following
      then Left (CannotElaborate name.span.start "Duplicate sequence-case constructor") else Right ()
    Right ((tag, branch) :: following)

  chooseExpectedSequenceMotiveGlobals : GlobalContext -> Position -> Context n -> Term n -> Term n -> Term n -> Term n -> Term n -> Either ResolveError (Term n)
  chooseExpectedSequenceMotiveGlobals shared position ctx ty scrutinee result base cons = do
    exact <- expectedDataMotive position ty result scrutinee
    case checkErasedGlobals shared checkingDepth typeReductionFuel ctx (SeqCase exact scrutinee base cons) result of
      Right () => Right exact
      Left _ => case guardedNormalGlobals shared typeReductionFuel scrutinee of
        Nothing => Left (CannotElaborate position "Cannot infer sequence-case motive; use an explicit return motive")
        Just normal => if sameSyntax normal scrutinee
          then Left (CannotElaborate position "Cannot infer sequence-case motive; use an explicit return motive")
          else do
            converted <- expectedDataMotive position ty result normal
            case checkErasedGlobals shared checkingDepth typeReductionFuel ctx (SeqCase converted scrutinee base cons) result of
              Right () => Right converted
              Left _ => Left (CannotElaborate position "Cannot infer sequence-case motive; use an explicit return motive")

  elaborateSequenceDataCaseGlobals : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> SourceSpan -> Term n -> Term n -> Term n -> Maybe Expr -> List (Token, List Token, Expr) -> Maybe (Term n) -> Either ResolveError (Term n)
  elaborateSequenceDataCaseGlobals shared globals ctx env span scrutinee ty element motive arms expected = do
    if typeNodes ty > inferredResultNodes || payloadSize ty > payloadLimit
      then Left (CannotElaborate span.start "Sequence-case type exceeds admission") else Right ()
    if length arms > 64 then Left (CannotElaborate span.start "Data-case branch admission exhausted (64)") else Right ()
    explicit <- the (Either ResolveError (Maybe (Term n))) $ case motive of
      Just authored => Just <$> elaborateInWithGlobals shared globals (Just ctx) env authored
      Nothing => Right Nothing
    let hint : Maybe (Term n)
        hint = case explicit of
          Just authored => Just authored
          Nothing => case expected of
            Just result => case expectedDataMotive span.start ty result scrutinee of
              Right candidate => Just candidate
              Left _ => Nothing
            Nothing => Nothing
    let boundedHint = case hint of
          Just candidate => if 5 + typeNodes candidate + typeNodes ty <= inferredResultNodes &&
                               payloadSize candidate + payloadSize ty <= payloadLimit then Just candidate else Nothing
          Nothing => Nothing
    let catchAll = case scrutinee of
          Variable i => index i env == "$clauseScrutinee"
          _ => False
    let clauseNames = if catchAll then map (\arm => fst arm) arms else []
    checked <- sequenceCaseArmsGlobals shared span.start globals ctx env ty element boundedHint clauseNames arms
    ordered <- orderDataArms span.start 0 [Nothing, Just (Linear, ty)] checked
    case ordered of
      [base, cons] => do
        selected <- case explicit of
          Just authored => Right authored
          Nothing => case expected of
            Just result => case constantSequenceResultGlobals shared span.start ctx base cons of
              Right common =>
                let constant = Lambda Erased ty (weaken common) in
                  case checkErasedGlobals shared checkingDepth typeReductionFuel ctx (SeqCase constant scrutinee base cons) result of
                    Right () => Right constant
                    Left _ => chooseExpectedSequenceMotiveGlobals shared span.start ctx ty scrutinee result base cons
              Left _ => chooseExpectedSequenceMotiveGlobals shared span.start ctx ty scrutinee result base cons
            Nothing => do
              result <- constantSequenceResultGlobals shared span.start ctx base cons
              Right (Lambda Erased ty (weaken result))
        Right (SeqCase selected scrutinee base cons)
      _ => Left (CannotElaborate span.start "Sequence case requires exactly two branches")

  -- A constructor named in a case arm: its index in the family, found from the global's value
  -- (`DataCon key index leading`), so a renamed or qualified import still resolves.
  familyArmIndex : GlobalContext -> Position -> List GlobalDefinition -> Vect n String -> String -> Token -> Either ResolveError Nat
  familyArmIndex shared position globals env key name = do
    if elem '.' (unpack name.spelling) then Right () else case lookupName name.spelling env of
      Just _ => Left (CannotElaborate name.span.start "Data-case constructor is shadowed by a local binder")
      Nothing => Right ()
    definition <- case find (\entry => entry.name == name.spelling) globals of
      Nothing => case qualifiedCandidates name.spelling globals of
        _ :: _ :: _ => Left (CannotElaborate name.span.start ("Ambiguous imported name " ++ name.spelling ++ "; use a qualified name"))
        _ => Left (Unbound name.span.start name.spelling)
      Just entry => Right entry
    case definition.value of
      DataCon other index _ => if other == key then Right index
        else Left (CannotElaborate name.span.start (name.spelling ++ " is a constructor of another family"))
      _ => Left (CannotElaborate name.span.start (name.spelling ++ " is not a constructor of this family"))

  fieldCount : Term m -> Nat
  fieldCount (Pi _ _ rest) = S (fieldCount rest)
  fieldCount _ = Z

  -- One arm: bind the constructor's fields (with the quantities of its type) and elaborate the
  -- body against the motive applied to the constructor rebuilt from them.
  familyArmBody : Nat -> GlobalContext -> List GlobalDefinition -> Context m -> Vect m String -> Term m -> List Token -> Term m ->
                  Maybe (Term m) -> SourceSpan -> Expr -> Either ResolveError (Term m)
  familyArmBody paramCount shared globals ctx env (Pi q domain rest) (binder :: binders) built motive span body = do
    inner <- familyArmBody paramCount shared globals (Extend ctx q domain) (binder.spelling :: env) rest binders
               (Apply (weaken built) (Variable FZ)) (map weaken motive) span body
    Right (Lambda q domain inner)
  familyArmBody paramCount shared globals ctx env (Pi _ _ _) [] built motive span body =
    Left (CannotElaborate span.start "Data-case constructor has more fields than its branch binds")
  familyArmBody paramCount shared globals ctx env _ (binder :: _) built motive span body =
    Left (CannotElaborate binder.span.start "Data-case constructor has fewer fields than its branch binds")
  familyArmBody paramCount shared globals ctx env resultType [] built motive span body = case motive of
    Nothing => elaborateInWithGlobals shared globals (Just ctx) env body
    Just chosen =>
      let indices = case dataTypeSpine resultType of
            Just (_, args) => drop paramCount args
            Nothing => []
          applied = Apply (applyAll chosen indices) built
          result = fromMaybe applied (guardedNormalGlobals shared typeReductionFuel applied) in
        elaborateExpectedGlobals shared globals ctx env result body

  familyArms : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> DataDecl -> List (Term n) ->
               Maybe (Term n) -> List Token -> List (Token, List Token, Expr) -> Either ResolveError (List (Nat, Term n))
  familyArms shared globals ctx env decl actuals motive clauseNames [] = Right []
  familyArms shared globals ctx env decl actuals motive clauseNames ((name, binders, body) :: rest) =
    if null rest && not (null clauseNames) && null binders && name.spelling == "_"
      then do
        covered <- traverse (familyArmIndex shared name.span.start globals env decl.key) (reverse (drop 1 (reverse clauseNames)))
        if length (nub covered) >= constructorCount decl
          then Left (CannotElaborate name.span.start "Catch-all clause is unreachable: every constructor is already matched")
          else familyCatchAllArms shared globals ctx env decl actuals motive name body covered (constructorCount decl) 0
      else do
        index <- familyArmIndex shared name.span.start globals env decl.key name
        closed <- case constructorType decl index of
          Nothing => Left (CannotElaborate name.span.start "Data-case constructor index is out of range")
          Just ty => Right (rename absurd ty)
        chain <- case instantiateParameters (take (parameterCount decl) actuals) closed of
          Left err => Left (CannotElaborate name.span.start (show err))
          Right ty => Right ty
        branch <- familyArmBody (parameterCount decl) shared globals ctx env chain binders (applyAll (DataCon decl.key index (parameterCount decl)) (take (parameterCount decl) actuals))
                    motive name.span body
        following <- familyArms shared globals ctx env decl actuals motive clauseNames rest
        if any (\entry => fst entry == index) following
          then Left (CannotElaborate name.span.start "Duplicate data-case constructor") else Right ()
        Right ((index, branch) :: following)

  ||| A final `_` clause: one arm per constructor not yet covered, every field bound
  ||| to `_` so a linear field is rejected by the ordinary usage check.
  familyCatchAllArms : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> DataDecl -> List (Term n) ->
                       Maybe (Term n) -> Token -> Expr -> List Nat -> Nat -> Nat -> Either ResolveError (List (Nat, Term n))
  familyCatchAllArms shared globals ctx env decl actuals motive name body covered Z index = Right []
  familyCatchAllArms shared globals ctx env decl actuals motive name body covered (S remaining) index = do
    later <- familyCatchAllArms shared globals ctx env decl actuals motive name body covered remaining (S index)
    if elem index covered then Right later else do
      closed <- case constructorType decl index of
        Nothing => Left (CannotElaborate name.span.start "Data-case constructor index is out of range")
        Just ty => Right (rename absurd ty)
      chain <- case instantiateParameters (take (parameterCount decl) actuals) closed of
        Left err => Left (CannotElaborate name.span.start (show err))
        Right ty => Right ty
      let blank : Token = name
      branch <- familyArmBody (parameterCount decl) shared globals ctx env chain (replicate (fieldCount chain) blank)
                  (applyAll (DataCon decl.key index (parameterCount decl)) (take (parameterCount decl) actuals)) motive name.span body
      Right ((index, branch) :: later)


  -- Missing arms are filled only for the inferred Nat-pattern motive. The
  -- resulting ordinary DataCase is checked with every constructor present.
  orderFamilyArms : GlobalContext -> Position -> DataDecl -> List (Term n) -> Bool -> Nat -> Nat -> List (Nat, Term n) -> Either ResolveError (List (Term n))
  orderFamilyArms shared position decl actuals fill Z index arms = Right []
  orderFamilyArms shared position decl actuals fill (S remaining) index arms = do
    branch <- case lookup index arms of
      Just branch => Right branch
      Nothing => case (if fill then missingIndexBranch shared decl index actuals else Nothing) of
        Just branch => Right branch
        Nothing => Left (CannotElaborate position "Data case does not cover every constructor that may be reachable")
    map (branch ::) (orderFamilyArms shared position decl actuals fill remaining (S index) arms)

  constantFamilyMotive : Nat -> Term n -> Term n -> Term n -> Either ResolveError (Term n)
  constantFamilyMotive Z indices family result = Right (Lambda Erased family (weaken result))
  constantFamilyMotive (S count) (Pi Erased domain body) family result =
    map (Lambda Erased domain) (constantFamilyMotive count body (Apply (weaken family) (Variable FZ)) (weaken result))
  constantFamilyMotive (S _) _ _ _ = Left (CannotElaborate (At 0 1 1) "Invalid index telescope")

  elaborateFamilyDataCaseGlobals : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> SourceSpan -> Term n -> Term n ->
                                   DataDecl -> List (Term n) -> Maybe Expr -> List (Token, List Token, Expr) -> Maybe (Term n) -> Either ResolveError (Term n)
  elaborateFamilyDataCaseGlobals shared globals ctx env span scrutinee ty decl actuals motive arms expected = do
    if length arms > 64 then Left (CannotElaborate span.start "Data-case branch admission exhausted (64)") else Right ()
    explicit <- the (Either ResolveError (Maybe (Term n))) $ case motive of
      Just authored => Just <$> elaborateInWithGlobals shared globals (Just ctx) env authored
      Nothing => Right Nothing
    let parameterArgs = take (parameterCount decl) actuals
    indexTypes <- case instantiateParameters parameterArgs (rename absurd (formerType decl)) of
      Left err => Left (CannotElaborate span.start (show err))
      Right chain => Right chain
    let family = applyAll (DataType decl.key) parameterArgs
    let catchAll = case scrutinee of
          Variable i => index i env == "$clauseScrutinee"
          _ => False
    let finish : Term n -> Bool -> Either ResolveError (Term n)
        finish = \selected, fill => do
          checked <- familyArms shared globals ctx env decl actuals (Just selected) (if catchAll then map (\arm => fst arm) arms else []) arms
          ordered <- orderFamilyArms shared span.start decl actuals fill (constructorCount decl) 0 checked
          let candidate = DataCase decl.key selected scrutinee ordered
          case expected of
            Nothing => Right candidate
            Just result => case checkErasedGlobals shared checkingDepth typeReductionFuel ctx candidate result of
              Left err => Left (CannotElaborate span.start ("Inferred indexed case: " ++ show err))
              Right () => Right candidate
    case (explicit, expected) of
      (Just selected, _) => finish selected False
      (Nothing, Just result) => do
        constant <- constantFamilyMotive (indexCount decl) indexTypes family result
        let small = case inferErasedGlobals shared checkingDepth typeReductionFuel ctx result of
              Right kind => case guardedNormalGlobals shared typeReductionFuel kind of
                Just (Universe 0) => True
                _ => False
              _ => False
        let directed : Maybe (Term n)
            directed = if small then case drop (parameterCount decl) actuals of
              [actual] => do
                normalized <- guardedNormalGlobals shared typeReductionFuel indexTypes
                index <- guardedNormalGlobals shared typeReductionFuel actual
                natFamilyMotive index normalized family result
              _ => Nothing else Nothing
        let inferred : Maybe (Term n, Bool)
            inferred = case directed of
              Just chosen => Just (chosen, True)
              Nothing => map (\chosen => (chosen, False))
                (abstractFamilyMotive (indexCount decl) (drop (parameterCount decl) actuals) indexTypes family result)
        case inferred of
          Nothing => finish constant False
          Just (chosen, fill) => case finish chosen fill of
            Right candidate => Right candidate
            Left first => case finish constant fill of
              Right candidate => Right candidate
              Left _ => Left first
      (Nothing, Nothing) => Left (CannotElaborate span.start "A case on this data needs an expected result type or an explicit motive")

  elaborateDataCaseGlobals : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> SourceSpan -> Expr -> Maybe Expr -> List (Token, List Token, Expr) -> Maybe (Term n) -> Either ResolveError (Term n)
  elaborateDataCaseGlobals shared globals ctx env span value motive arms expected = do
    scrutinee <- elaborateInWithGlobals shared globals (Just ctx) env value
    inferred <- case inferErasedGlobals shared checkingDepth typeReductionFuel ctx scrutinee of
      Left err => Left (CannotElaborate span.start ("Cannot infer data-case scrutinee: " ++ show err))
      Right ty => Right ty
    case weakHeadGlobals (globalValue shared) typeReductionFuel inferred of
      HeadForm ty@NatType => elaborateNatDataCaseGlobals shared globals ctx env span scrutinee ty motive arms expected
      HeadForm ty@(RecType _) => elaborateRecursiveDataCaseGlobals shared globals ctx env span scrutinee ty motive arms expected
      HeadForm ty@(SeqType _ element) => elaborateSequenceDataCaseGlobals shared globals ctx env span scrutinee ty element motive arms expected
      HeadForm ty@(NominalType _ _ _) => elaborateNominalDataCaseGlobals shared globals ctx env span scrutinee ty motive arms expected
      HeadLimit _ => Left (CannotElaborate span.start "Data-case scrutinee reduction budget exhausted")
      HeadForm ty => case dataTypeSpine ty of
        Just (key, actuals) => case dataDeclaration shared key of
          Just decl => elaborateFamilyDataCaseGlobals shared globals ctx env span scrutinee ty decl actuals motive arms expected
          Nothing => Left (CannotElaborate span.start "Data case requires a supported nominal or recursive data scrutinee")
        Nothing => Left (CannotElaborate span.start "Data case requires a supported nominal or recursive data scrutinee")

  elaborateNominalDataCaseGlobals : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> SourceSpan -> Term n -> Term n -> Maybe Expr -> List (Token, List Token, Expr) -> Maybe (Term n) -> Either ResolveError (Term n)
  elaborateNominalDataCaseGlobals shared globals ctx env span scrutinee nominal motive arms expected = do
    let context = Just ctx
    if coreNodes nominal > 512 then Left (CannotElaborate span.start "Data-case nominal type exceeds 512 nodes") else Right ()
    shape <- the (Either ResolveError (Term n)) $ case nominal of
      NominalType _ _ shape => case weakHeadGlobals (globalValue shared) typeReductionFuel shape of
        HeadForm shape@(VariantType _) => Right shape
        HeadLimit _ => Left (CannotElaborate span.start "Data-case shape reduction budget exhausted")
        _ => Left (CannotElaborate span.start "Data-case nominal shape is not a variant")
      _ => Left (CannotElaborate span.start "Invalid data-case nominal type")
    case shape of
      VariantType descriptors => do
        if length descriptors > 64 then Left (CannotElaborate span.start "Data-case branch admission exhausted (64)") else Right ()
        let indices = case nominal of NominalType _ args _ => args; _ => []
        explicit <- the (Either ResolveError (Maybe (Term n))) $ case motive of
          Just authored => Just <$> elaborateInWithGlobals shared globals context env authored
          Nothing => Right Nothing
        let hint : Maybe (Term n)
            hint = case explicit of
              Just authored => Just authored
              Nothing => case expected of
                Just result => case expectedDataMotive span.start nominal result scrutinee of
                  Right candidate => Just candidate
                  Left _ => Nothing
                Nothing => Nothing
        let boundedHint = case hint of
              Just candidate => if typeNodes candidate <= inferredResultNodes then Just candidate else Nothing
              Nothing => Nothing
        let catchAll = case scrutinee of
              Variable i => index i env == "$clauseScrutinee"
              _ => False
        checked <- elaborateDataArmsGlobals shared globals ctx env nominal shape indices descriptors boundedHint (if catchAll then map (\arm => fst arm) arms else []) arms
        ordered <- orderDataArms span.start 0 descriptors checked
        selected <- case explicit of
          Just authored => Right authored
          Nothing => case (expected, scrutinee) of
            (Just result, _) =>
              -- Retain a previously accepted constant motive only if it also
              -- checks against this expected type. This probe is erased-only;
              -- the completed declaration is independently checked again. Do
              -- not impose the abstraction size limit on the constant path.
              case constantDataResultGlobals shared span.start ctx descriptors ordered of
                Right common =>
                  let constant = Lambda Erased nominal (weaken common)
                      candidate = assembleDataCase nominal shape constant scrutinee ordered in
                    case checkErasedGlobals shared checkingDepth typeReductionFuel ctx candidate result of
                      Right () => Right constant
                      Left _ => chooseExpectedMotiveGlobals shared span.start ctx nominal shape scrutinee result ordered
                Left _ => chooseExpectedMotiveGlobals shared span.start ctx nominal shape scrutinee result ordered
            _ => do
              result <- constantDataResultGlobals shared span.start ctx descriptors ordered
              Right (Lambda Erased nominal (weaken result))
        Right (assembleDataCase nominal shape selected scrutinee ordered)
      _ => Left (CannotElaborate span.start "Invalid data-case shape")

  equationBodyGlobals : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> Term n -> List Token -> Expr -> Either ResolveError (Term n)
  equationBodyGlobals shared globals context env expected [argument] body@(NDataCase span (NRef _ scrutinee) Nothing [(zero, [], base), (binder, [], more)]) =
    if argument.spelling /= "$clauseScrutinee" || scrutinee /= argument.spelling ||
       not (binder.spelling == "_" || (case unpack binder.spelling of c :: _ => isLower c; [] => False)) ||
       isJust (lookupName binder.spelling env) ||
       isJust (find (\entry => entry.name == binder.spelling) globals) ||
       not (null (qualifiedCandidates binder.spelling globals))
    then ordinaryEquationGlobals shared globals context env expected argument body
    else case expected of
      Pi q domain result => do
        if coreNodes domain > 512 then Left (CannotElaborate argument.span.start "Function equation parameter type exceeds 512 nodes") else Right ()
        if not (maybe False (\ty => sameSyntax ty NatType) (guardedNormalGlobals shared typeReductionFuel domain))
          then ordinaryEquationGlobals shared globals context env expected argument body else do
          let ctx = Extend context q domain
          let scope = argument.spelling :: env
          motive <- expectedDataMotive span.start NatType result (Variable FZ)
          checked <- natCaseArmsGlobals shared span.start Linear globals ctx scope NatType (Just motive) [(zero, [], base)]
          case checked of
            [(0, baseTerm)] => do
              let successorContext = Extend ctx Unrestricted NatType
              let actual = NatSucc (Variable FZ)
              let applied = Apply (weaken motive) actual
              let branchResult = fromMaybe applied (guardedNormalGlobals shared typeReductionFuel applied)
              branch <- elaborateExpectedGlobals shared globals (Extend successorContext Unrestricted NatType)
                          (binder.spelling :: "$nat.predecessor" :: scope) (weaken branchResult) more
              let successor = Lambda Unrestricted NatType
                    (Apply (Lambda Unrestricted NatType branch) actual)
              Right (Lambda q domain (NatCase motive (Variable FZ) baseTerm successor))
            _ => Left (CannotElaborate zero.span.start "Nat catch-all requires Zero as its first clause")
      _ => ordinaryEquationGlobals shared globals context env expected argument body
  equationBodyGlobals shared globals context env expected [] body = elaborateExpectedGlobals shared globals context env expected body
  equationBodyGlobals shared globals context env expected (name :: rest) body = do
    -- Do not reduce an unchecked signature to expose Pi: head beta reduction
    -- can expand before any post-reduction node bound. Explicit Pi syntax is
    -- the deliberately narrower, pre-clone-accounted first slice.
    case expected of
      Pi q domain result => do
        if coreNodes domain > 512 then Left (CannotElaborate name.span.start "Function equation parameter type exceeds 512 nodes") else Right ()
        following <- equationBodyGlobals shared globals (Extend context q domain) (name.spelling :: env) result rest body
        Right (Lambda q domain following)
      _ => Left (CannotElaborate name.span.start "Function equation requires an explicit Pi for every named parameter")

  ordinaryEquationGlobals : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> Term n -> Token -> Expr -> Either ResolveError (Term n)
  ordinaryEquationGlobals shared globals context env expected name body = case expected of
    Pi q domain result => do
      if coreNodes domain > 512 then Left (CannotElaborate name.span.start "Function equation parameter type exceeds 512 nodes") else Right ()
      following <- equationBodyGlobals shared globals (Extend context q domain) (name.spelling :: env) result [] body
      Right (Lambda q domain following)
    _ => Left (CannotElaborate name.span.start "Function equation requires an explicit Pi for every named parameter")

  elaborateArmsGlobals : GlobalContext -> List GlobalDefinition -> Maybe (Context n) -> Vect n String -> List (Maybe (Quantity, Expr)) -> Either ResolveError (List (Maybe (Quantity, Term n)))
  elaborateArmsGlobals shared globals context env [] = Right []
  elaborateArmsGlobals shared globals context env (Nothing :: xs) = (Nothing ::) <$> elaborateArmsGlobals shared globals context env xs
  elaborateArmsGlobals shared globals context env (Just (q, ty) :: xs) = do
    ty <- elaborateInWithGlobals shared globals context env ty
    rest <- elaborateArmsGlobals shared globals context env xs
    Right (Just (q, ty) :: rest)

  ||| Resolve with newest-first names. Binder domains see the old environment;
  ||| bodies see the new binder. Shadowing resolves to the nearest binder.
  ||| Underscore is a wildcard and cannot be referenced.
  public export
  elaborateInWithGlobals : GlobalContext -> List GlobalDefinition -> Maybe (Context n) -> Vect n String -> Expr -> Either ResolveError (Term n)
  elaborateInWithGlobals shared globals context env (NRef span name) =
    if scopeProbe name && isNothing (lookupName name env) && isNothing (lookupGlobal name globals) then Left (scopeFailure shared globals context env Nothing span.start name)
    else if name == "_" then Left (Unbound span.start name)
       else case lookupName name env of
         Nothing => case lookupGlobal name globals of
           Nothing => case qualifiedCandidates name globals of
             candidates@(_ :: _ :: _) => Left (CannotElaborate span.start (ambiguityMessage name candidates))
             _ => Left (Unbound span.start name)
           Just value => Right (rename absurd value)
         Just index => Right (Variable index)
  elaborateInWithGlobals shared globals context env (NQualifiedRef span name) =
    case lookupGlobal name globals of
      Nothing => Left (Unbound span.start name)
      Just value => Right (rename absurd value)
  elaborateInWithGlobals shared globals context env (NSort span level) = Right (Universe level)
  elaborateInWithGlobals shared globals context env (NUnitType span) = Right UnitType
  elaborateInWithGlobals shared globals context env (NUnitValue span) = Right UnitValue
  elaborateInWithGlobals shared globals context env (NStringType span) = Right StringType
  elaborateInWithGlobals shared globals context env (NStringValue span value) = Right (StringValue value)
  -- A numeric literal denotes the built-in Nat value directly, never the names Zero/Succ,
  -- so a user binding of those names cannot change what a literal means.
  elaborateInWithGlobals shared globals context env (NNatValue span value) = Right (naturalTerm value)
  elaborateInWithGlobals shared globals context env (NWordValue span value) =
    if value >= wordModulus then Left (CannotElaborate span.start "Word literal exceeds 2^64-1") else Right (wordTerm value)
  elaborateInWithGlobals shared globals context env (NBoolType span) = Right BoolType
  elaborateInWithGlobals shared globals context env (NBoolValue span True) = Right BoolTrue
  elaborateInWithGlobals shared globals context env (NBoolValue span False) = Right BoolFalse
  elaborateInWithGlobals shared globals context env (NIf span condition yes no) =
    [| BoolCase (elaborateInWithGlobals shared globals context env condition) (elaborateInWithGlobals shared globals context env yes) (elaborateInWithGlobals shared globals context env no) |]
  elaborateInWithGlobals shared globals context env (NUnitCase span scrutinee body) =
    [| UnitCase (elaborateInWithGlobals shared globals context env scrutinee) (elaborateInWithGlobals shared globals context env body) |]
  elaborateInWithGlobals shared globals context env (NSigma span q r name domain body) = do
    domain <- elaborateInWithGlobals shared globals context env domain
    body <- elaborateInWithGlobals shared globals (map (\ctx => Extend ctx q domain) context) (name :: env) body
    Right (Sigma q r domain body)
  elaborateInWithGlobals shared globals context env (NPairValue span ty first second) =
    [| PairValue (elaborateInWithGlobals shared globals context env ty) (elaborateInWithGlobals shared globals context env first) (elaborateInWithGlobals shared globals context env second) |]
  elaborateInWithGlobals shared globals context env (NRecType _ key) = Right (RecType key)
  elaborateInWithGlobals shared globals context env (NRecEnd _ ty) = RecEnd <$> elaborateInWithGlobals shared globals context env ty
  elaborateInWithGlobals shared globals context env (NRecMore _ ty tail) = [| RecMore (elaborateInWithGlobals shared globals context env ty) (elaborateInWithGlobals shared globals context env tail) |]
  elaborateInWithGlobals shared globals context env (NRecFold _ motive base next value) = [| RecFold (elaborateInWithGlobals shared globals context env motive) (elaborateInWithGlobals shared globals context env base) (elaborateInWithGlobals shared globals context env next) (elaborateInWithGlobals shared globals context env value) |]
  elaborateInWithGlobals shared globals context env (NSeqType _ key element) = SeqType key <$> elaborateInWithGlobals shared globals context env element
  elaborateInWithGlobals shared globals context env (NSeqNil _ ty) = SeqNil <$> elaborateInWithGlobals shared globals context env ty
  elaborateInWithGlobals shared globals context env (NSeqCons _ ty head tail) = [| SeqCons (elaborateInWithGlobals shared globals context env ty) (elaborateInWithGlobals shared globals context env head) (elaborateInWithGlobals shared globals context env tail) |]
  elaborateInWithGlobals shared globals context env (NSeqFold _ motive base next value) = [| SeqFold (elaborateInWithGlobals shared globals context env motive) (elaborateInWithGlobals shared globals context env base) (elaborateInWithGlobals shared globals context env next) (elaborateInWithGlobals shared globals context env value) |]
  elaborateInWithGlobals shared globals context env (NDataType _ key) = Right (DataType key)
  elaborateInWithGlobals shared globals context env (NDataCon _ key index leading) = Right (DataCon key index leading)
  elaborateInWithGlobals shared globals context env (NNominalType span key indices shape) = do
    indices <- elaborateTermsGlobals shared globals context env indices
    shape <- elaborateInWithGlobals shared globals context env shape
    recursive <- case mentionsNominalGlobals shared key shape of
      Left message => Left (CannotElaborate span.start message)
      Right recursive => Right recursive
    if recursive then Left (CannotElaborate span.start "Recursive data is not supported") else Right ()
    Right (NominalType key indices shape)
  elaborateInWithGlobals shared globals context env (NNominalValue _ ty value) = [| NominalValue (elaborateInWithGlobals shared globals context env ty) (elaborateInWithGlobals shared globals context env value) |]
  elaborateInWithGlobals shared globals context env (NNominalCase _ motive value branch) = [| NominalCase (elaborateInWithGlobals shared globals context env motive) (elaborateInWithGlobals shared globals context env value) (elaborateInWithGlobals shared globals context env branch) |]
  elaborateInWithGlobals shared globals context env (NVariantType _ arms) = VariantType <$> elaborateArmsGlobals shared globals context env arms
  elaborateInWithGlobals shared globals context env (NVariantValue _ ty tag Nothing) = (\t => VariantValue t tag Nothing) <$> elaborateInWithGlobals shared globals context env ty
  elaborateInWithGlobals shared globals context env (NVariantValue _ ty tag (Just value)) = [| VariantValue (elaborateInWithGlobals shared globals context env ty) (pure tag) (Just <$> elaborateInWithGlobals shared globals context env value) |]
  elaborateInWithGlobals shared globals context env (NVariantCase _ motive value branches) = [| VariantCase (elaborateInWithGlobals shared globals context env motive) (elaborateInWithGlobals shared globals context env value) (elaborateTermsGlobals shared globals context env branches) |]
  elaborateInWithGlobals shared globals context env (NBoxType span q ty) = [| BoxType (pure q) (elaborateInWithGlobals shared globals context env ty) |]
  elaborateInWithGlobals shared globals context env (NBoxValue span ty value) = [| BoxValue (elaborateInWithGlobals shared globals context env ty) (elaborateInWithGlobals shared globals context env value) |]
  elaborateInWithGlobals shared globals context env (NBoxCase span motive value branch) =
    [| BoxCase (elaborateInWithGlobals shared globals context env motive) (elaborateInWithGlobals shared globals context env value) (elaborateInWithGlobals shared globals context env branch) |]
  elaborateInWithGlobals shared globals context env (NDataCase span value motive arms) = do
    ctx <- case context of Nothing => Left (CannotElaborate span.start "Data case requires a typed context"); Just ctx => Right ctx
    elaborateDataCaseGlobals shared globals ctx env span value motive arms Nothing
  elaborateInWithGlobals shared globals context env (NEquationLambda span names signature body) = do
    ctx <- case context of Nothing => Left (CannotElaborate span.start "Function equations require a typed context"); Just ctx => Right ctx
    expected <- elaborateSignatureGlobals shared globals context env signature
    equationBodyGlobals shared globals ctx env expected names body
  elaborateInWithGlobals shared globals context env (NPatternLambda span _ _) =
    Left (CannotElaborate span.start "Inferred field binders require a constructor-named pattern")
  elaborateInWithGlobals shared globals context env (NCaseEither span asRecord asData) =
    case elaborateInWithGlobals shared globals context env asRecord of
      Right term => Right term
      Left failure => case elaborateInWithGlobals shared globals context env asData of
        Right term => Right term
        Left other => if isJust other.completion then Left other else Left failure
  elaborateInWithGlobals shared globals context env (NConstructorCase span arity constructor scrutinee branch motive) = do
    if not (namedConstructor constructor)
       then Left (CannotElaborate (extent constructor).start "Pattern constructor must be a named function, optionally explicitly instantiated") else Right ()
    typedContext <- case context of
      Nothing => Left (CannotElaborate span.start "Named pattern checking requires a typed context")
      Just ctx => Right ctx
    candidate <- elaborateInWithGlobals shared globals context env constructor
    value <- elaborateInWithGlobals shared globals context env scrutinee
    named <- instantiateParametersGlobals shared (extent constructor).start arity typedContext candidate value
    branch <- elaboratePatternBranchGlobals shared globals typedContext env (extent constructor).start arity named branch
    case motive of
      Nothing => inferCaseGlobals shared span.start arity typedContext value branch
      Just authored => do
        explicit <- elaborateInWithGlobals shared globals context env authored
        Right (if arity == 1 then BoxCase explicit value branch else PairCase explicit value branch)
  elaborateInWithGlobals shared globals context env (NInferCase span arity scrutinee branch) = do
    typedContext <- case context of
      Nothing => Left (CannotElaborate span.start "Motive inference requires a typed context; use contextual expression elaboration")
      Just ctx => Right ctx
    value <- elaborateInWithGlobals shared globals context env scrutinee
    branch <- elaborateInWithGlobals shared globals context env branch
    inferCaseGlobals shared span.start arity typedContext value branch
  elaborateInWithGlobals shared globals context env (NPairCase span motive value branch) =
    [| PairCase (elaborateInWithGlobals shared globals context env motive) (elaborateInWithGlobals shared globals context env value) (elaborateInWithGlobals shared globals context env branch) |]
  elaborateInWithGlobals shared globals context env (NImplicitPi span _ _ _ _) =
    Left (CannotElaborate span.start "Implicit binders are supported only as the leading binder of a module declaration signature")
  elaborateInWithGlobals shared globals context env (NConstraintPi span q name domain body) = do
    domain <- elaborateInWithGlobals shared globals context env domain
    constraintTypeGlobals shared span.start q domain
    body <- elaborateInWithGlobals shared globals (map (\ctx => Extend ctx q domain) context) (name :: env) body
    Right (Pi q domain body)
  elaborateInWithGlobals shared globals context env (NImplementationApply span origin function) = do
    typed <- case context of
      Nothing => Left (CannotElaborate origin.start "Implementation lookup requires a typed context")
      Just ctx => Right ctx
    function <- elaborateInWithGlobals shared globals context env function
    selectImplementationGlobals shared origin.start globals typed function
  elaborateInWithGlobals shared globals context env (NDictionaryApply span origin function argument) = do
    typed <- case context of
      Nothing => Left (CannotElaborate origin.start "Dictionary selection requires a typed context")
      Just ctx => Right ctx
    function <- elaborateInWithGlobals shared globals context env function
    argument <- case argument of
      Nothing => Right Nothing
      Just value => Just <$> elaborateInWithGlobals shared globals context env value
    selectDictionaryGlobals shared origin.start typed env function argument
  elaborateInWithGlobals shared globals context env (NPi span q name domain body) = do
    domain <- elaborateInWithGlobals shared globals context env domain
    body <- elaborateInWithGlobals shared globals (map (\ctx => Extend ctx q domain) context) (name :: env) body
    Right (Pi q domain body)
  elaborateInWithGlobals shared globals context env (NLambda span q name domain body) = do
    authored <- elaborateInWithGlobals shared globals context env domain
    let domain = fromMaybe authored (familyAnnotation shared authored)
    body <- elaborateInWithGlobals shared globals (map (\ctx => Extend ctx q domain) context) (name :: env) body
    Right (Lambda q domain body)
  -- Chains are grouped by module checking, where imported fixities are known. A chain that
  -- reaches here was parsed outside a named module, so its grouping would be a guess.
  elaborateInWithGlobals shared globals context env (NOperators span _ _) =
    Left (CannotElaborate span.start "Symbolic operators require a named module so their fixity is known; use prefix application")
  elaborateInWithGlobals shared globals context env (NInfix span function left right) = do
    operator <- elaborateInWithGlobals shared globals context env function
    first <- elaborateApplicationGlobals shared globals context env operator left
    elaborateApplicationGlobals shared globals context env first right
  elaborateInWithGlobals shared globals context env expression@(NApply span sourceFunction argument) =
    if hasImplicitCall globals env expression then do
      ctx <- case context of
        Nothing => Left (CannotElaborate span.start "Implicit insertion requires a typed context; use explicit {arguments}")
        Just ctx => Right ctx
      elaborateImplicitCallGlobals shared globals ctx env Nothing expression
    else do
      function <- elaborateInWithGlobals shared globals context env sourceFunction
      elaborateApplicationGlobals shared globals context env function argument
  elaborateInWithGlobals shared globals context env expression@(NImplicitApply span sourceFunction argument) = do
    ctx <- case context of
      Nothing => Left (CannotElaborate span.start "Explicit {arguments} require a typed context")
      Just ctx => Right ctx
    elaborateImplicitCallGlobals shared globals ctx env Nothing expression

  elaborateInWithGlobals shared globals context env (NSequence span first rest) = do
    action <- elaborateInWithGlobals shared globals context env first
    following <- elaborateInWithGlobals shared globals context env rest
    Right (IOBind UnitType UnitType action
      (Lambda Linear UnitType (UnitCase (Variable FZ) (weaken following))))
  elaborateInWithGlobals shared globals context env (NDoBind span name domain action body) = do
    ty <- elaborateInWithGlobals shared globals context env domain
    action <- elaborateInWithGlobals shared globals context env action
    body <- elaborateInWithGlobals shared globals (map (\ctx => Extend ctx Linear ty) context) (name :: env) body
    Right (IOBind ty UnitType action (Lambda Linear ty body))
  -- Checking an identity application enforces the expected domain using existing
  -- typing/compatibility rules. Linear use preserves the term's runtime usage.
  elaborateInWithGlobals shared globals context env (NAscribe span term expected) = do
    ty <- elaborateInWithGlobals shared globals context env expected
    term <- case context of
      Just ctx => elaborateExpectedGlobals shared globals ctx env ty term
      Nothing => elaborateInWithGlobals shared globals context env term
    Right (Apply (Lambda Linear ty (Variable FZ)) term)

  -- The binding is nonrecursive: annotation and value use the outer environment.
  -- A lambda/application enforces the annotation and declared resource quantity.
  elaborateInWithGlobals shared globals context env (NLet span q name expected value body) = do
    ty <- elaborateInWithGlobals shared globals context env expected
    value <- case context of
      Just ctx => elaborateExpectedGlobals shared globals ctx env ty value
      Nothing => elaborateInWithGlobals shared globals context env value
    body <- elaborateInWithGlobals shared globals (map (\ctx => Extend ctx q ty) context) (name :: env) body
    Right (Apply (Lambda q ty body) value)

  elaborateInWithGlobals shared globals context env (NDoResult span result body) = do
    ty <- elaborateInWithGlobals shared globals context env result
    value <- elaborateDoGlobals shared globals context env ty body
    Right (Apply (Lambda Linear (IOType ty) (Variable FZ)) value)

  -- Traverse the authored spine structurally. Arguments are elaborated only
  -- as direct source subexpressions, preserving totality and source order.
  collectImplicitCallGlobals : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> Expr -> Either ResolveError (PendingImplicit n)
  collectImplicitCallGlobals shared globals context env (NImplicitApply span function argument) = do
    pending <- collectImplicitCallGlobals shared globals context env function
    if not (null pending.ordinary) || isJust pending.applied
      then Left (CannotElaborate span.start "Explicit {arguments} must precede ordinary arguments") else Right ()
    if length pending.given >= pending.entry.implicitPrefix
      then Left (CannotElaborate span.start "Too many explicit {arguments}") else Right ()
    value <- elaborateInWithGlobals shared globals (Just context) env argument
    Right ({ given := pending.given ++ [value] } pending)
  collectImplicitCallGlobals shared globals context env (NApply span function argument) = do
    pending <- collectImplicitCallGlobals shared globals context env function
    case pending.applied of
      Just function => do
        result <- elaborateApplicationGlobals shared globals (Just context) env function argument
        Right ({ applied := Just result } pending)
      Nothing => if length pending.given == pending.entry.implicitPrefix then do
          filled <- insertDictionariesGlobals shared span.start globals context env pending.entry.autoConstraints
                      (foldl Apply pending.function pending.given)
          result <- elaborateApplicationGlobals shared globals (Just context) env filled argument
          Right ({ applied := Just result } pending)
        else do
          if length pending.ordinary >= implicitTelescopeLimit
            then Left (CannotElaborate span.start "Implicit inference telescope admission exhausted (64)") else Right ()
          value <- elaborateInWithGlobals shared globals (Just context) env argument
          proposed <- implicitArgumentTypeGlobals shared span.start implicitProposalDepth context value
          state <- case pending.solver of
            Just state => Right state
            Nothing => do
              begun <- beginImplicit span.start pending.entry.implicitPrefix
                         (rename absurd pending.entry.declaredType) pending.given
              skipConstraintsGlobals shared span.start pending.entry.autoConstraints begun
          state <- advanceImplicitGlobals shared span.start state proposed
          let values = pending.ordinary ++ [value]
          if implicitSolved state then do
            inferred <- finishImplicitGlobals shared span.start context state Nothing
            filled <- insertDictionariesGlobals shared span.start globals context env pending.entry.autoConstraints
                        (foldl Apply pending.function inferred)
            Right ({ applied := Just (foldl Apply filled values), ordinary := [], solver := Nothing } pending)
            else Right ({ ordinary := values, solver := Just state } pending)
  collectImplicitCallGlobals shared globals context env head = do
    entry <- case implicitHead globals env head of
      Nothing => Left (implicitHeadFailure globals env head)
      Just entry => Right entry
    value <- case lookupGlobal entry.name globals of
      Nothing => Left (CannotElaborate (extent head).start "Implicit global is unavailable")
      Just value => Right (rename absurd value)
    Right (PendingCall entry value [] [] Nothing Nothing)

  elaborateImplicitCallGlobals : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> Maybe (Term n) -> Expr -> Either ResolveError (Term n)
  elaborateImplicitCallGlobals shared globals context env expected source = do
    let (head, args) = applicationSpine source
    entry <- case implicitHead globals env head of
      Nothing => Left (implicitHeadFailure globals env head)
      Just entry => Right entry
    if entry.implicitPrefix > implicitTelescopeLimit
      then Left (CannotElaborate (extent source).start "Implicit telescope admission exhausted (64)") else Right ()
    needsInference <- spineAdmission (extent source).start entry.implicitPrefix args
    if needsInference && typeNodes entry.declaredType > inferredParameterNodes
      then Left (CannotElaborate (extent source).start "Implicit function type exceeds 512 nodes; use explicit {arguments}") else Right ()
    if needsInference && payloadSize entry.declaredType > payloadLimit
      then Left (CannotElaborate (extent source).start "Implicit function type exceeds payload admission; use explicit {arguments}") else Right ()
    pending <- collectImplicitCallGlobals shared globals context env source
    case pending.applied of
      Just result => Right result
      Nothing => if null pending.ordinary
        then Right (foldl Apply pending.function pending.given)
        else do
          if typeNodes pending.entry.declaredType > inferredParameterNodes
            then Left (CannotElaborate (extent source).start "Implicit function type exceeds 512 nodes; use explicit {arguments}") else Right ()
          if payloadSize pending.entry.declaredType > payloadLimit
            then Left (CannotElaborate (extent source).start "Implicit function type exceeds payload admission; use explicit {arguments}") else Right ()
          state <- case pending.solver of
            Just state => Right state
            Nothing => Left (CannotElaborate (extent source).start "Implicit inference state is unavailable")
          inferred <- finishImplicitGlobals shared (extent source).start context state expected
          filled <- insertDictionariesGlobals shared (extent source).start globals context env pending.entry.autoConstraints
                      (foldl Apply pending.function inferred)
          Right (foldl Apply filled pending.ordinary)

  elaborateApplicationGlobals : GlobalContext -> List GlobalDefinition -> Maybe (Context n) -> Vect n String -> Term n -> Expr -> Either ResolveError (Term n)
  elaborateApplicationGlobals shared globals context env function argument = do
    argument <- case context of
      Just ctx => if wantsExpected argument || hasImplicitCall globals env argument then
        case inferErasedGlobals shared checkingDepth typeReductionFuel ctx function of
          Right (Pi _ domain _) =>
            if typeNodes domain <= inferredResultNodes
              then elaborateExpectedGlobals shared globals ctx env domain argument
              else elaborateInWithGlobals shared globals context env argument
          _ => elaborateInWithGlobals shared globals context env argument
        else elaborateInWithGlobals shared globals context env argument
      Nothing => elaborateInWithGlobals shared globals context env argument
    let applied = Apply function argument
    Right (fromMaybe applied (sequenceApplication shared applied))

  elaboratePatternBranchGlobals : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> Position ->
                           Nat -> Term n -> Expr -> Either ResolveError (Term n)
  elaboratePatternBranchGlobals shared globals context env position arity constructor (NPatternLambda span names body) = do
    fields <- inferConstructorFieldsGlobals shared position arity context constructor
    case (fields, names) of
      (OneField q domain, [name]) => do
        body <- elaborateInWithGlobals shared globals (Just (Extend context q domain)) (name.spelling :: env) body
        Right (Lambda q domain body)
      (TwoFields q domain r second, [first, last]) => do
        body <- elaborateInWithGlobals shared globals (Just (Extend (Extend context q domain) r second))
                  (last.spelling :: first.spelling :: env) body
        Right (Lambda q domain (Lambda r second body))
      _ => Left (CannotElaborate span.start "Constructor field count does not match the pattern names")
  elaboratePatternBranchGlobals shared globals context env position arity constructor branch = do
    resolved <- elaborateInWithGlobals shared globals (Just context) env branch
    checkConstructorGlobals shared position arity context constructor resolved
    Right resolved

  -- The block result is resolved outside its statements and weakened under each
  -- local binder. It must never be re-resolved under a shadowing statement name.
  elaborateDoGlobals : GlobalContext -> List GlobalDefinition -> Maybe (Context n) -> Vect n String -> Term n -> Expr ->
              Either ResolveError (Term n)
  elaborateDoGlobals shared globals context env result (NSequence span first rest) = do
    action <- elaborateInWithGlobals shared globals context env first
    following <- elaborateDoGlobals shared globals context env result rest
    Right (IOBind UnitType result action
      (Lambda Linear UnitType (UnitCase (Variable FZ) (weaken following))))
  elaborateDoGlobals shared globals context env result (NDoBind span name domain action body) = do
    ty <- elaborateInWithGlobals shared globals context env domain
    action <- elaborateInWithGlobals shared globals context env action
    body <- elaborateDoGlobals shared globals (map (\ctx => Extend ctx Linear ty) context) (name :: env) (weaken result) body
    Right (IOBind ty result action (Lambda Linear ty body))
  elaborateDoGlobals shared globals context env result (NLet span q name expected value body) = do
    ty <- elaborateInWithGlobals shared globals context env expected
    value <- case context of
      Just ctx => elaborateExpectedGlobals shared globals ctx env ty value
      Nothing => elaborateInWithGlobals shared globals context env value
    body <- elaborateDoGlobals shared globals (map (\ctx => Extend ctx q ty) context) (name :: env) (weaken result) body
    Right (Apply (Lambda q ty body) value)
  elaborateDoGlobals shared globals context env result term = case context of
    Just ctx => elaborateExpectedGlobals shared globals ctx env (IOType result) term
    Nothing => elaborateInWithGlobals shared globals context env term

||| Contextual elaboration of a closed source expression.
public export
elaborateClosedWithGlobals : GlobalContext -> List GlobalDefinition -> Expr -> Either ResolveError (Term 0)
elaborateClosedWithGlobals shared globals = elaborateInWithGlobals shared globals (Just Empty) []

public export
elaborateClosedGlobals : GlobalContext -> Expr -> Either ResolveError (Term 0)
elaborateClosedGlobals shared = elaborateClosedWithGlobals shared []

-- Closed-syntax compatibility APIs. Shared programs pass their checked context explicitly.
public export
elaborateClosed : Expr -> Either ResolveError (Term 0)
elaborateClosed = elaborateClosedGlobals emptyGlobals

public export
elaborateClosedWith : List GlobalDefinition -> Expr -> Either ResolveError (Term 0)
elaborateClosedWith = elaborateClosedWithGlobals emptyGlobals

public export
elaborateExpected : List GlobalDefinition -> Context n -> Vect n String -> Term n -> Expr -> Either ResolveError (Term n)
elaborateExpected = elaborateExpectedGlobals emptyGlobals

public export
elaborateInWith : List GlobalDefinition -> Maybe (Context n) -> Vect n String -> Expr -> Either ResolveError (Term n)
elaborateInWith = elaborateInWithGlobals emptyGlobals

public export
elaborateSignature : List GlobalDefinition -> Maybe (Context n) -> Vect n String -> Expr -> Either ResolveError (Term n)
elaborateSignature = elaborateSignatureGlobals emptyGlobals

public export
elaborateSignatureWith : Bool -> List GlobalDefinition -> Maybe (Context n) -> Vect n String -> Expr -> Either ResolveError (Term n)
elaborateSignatureWith = elaborateSignatureWithGlobals emptyGlobals
