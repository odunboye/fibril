-- Contextual named-to-core elaboration; ordinary core checking remains independent.
module Fibril.Elaboration.Expression

import Data.Fin
import Data.List
import Data.Vect
import Fibril.Core.Size
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Global
import public Fibril.Source.Resolve.Error
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Reduction
import Fibril.Core.Limits
import Fibril.Core.WeakHead
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

boundedResult : Position -> Term n -> Either ResolveError (Term n)
boundedResult position result = do
  if typeNodes result > inferredResultNodes then Left (CannotElaborate position "Inferred motive result type exceeds 512 nodes; use an explicit return motive") else Right ()
  normal <- case normalize typeReductionFuel result of
    Normal value => Right value
    OutOfFuel _ => Left (CannotElaborate position "Motive inference reduction budget exhausted; use an explicit return motive")
  if typeNodes normal > inferredResultNodes then Left (CannotElaborate position "Inferred motive result type exceeds 512 nodes; use an explicit return motive") else Right normal

inferCase : Position -> Nat -> Context n -> Term n -> Term n -> Either ResolveError (Term n)
inferCase position arity context scrutinee branch = do
  branchType <- case inferErased checkingDepth typeReductionFuel context branch of
    Left err => Left (CannotElaborate position ("Cannot infer record branch type: " ++ show err))
    Right ty => Right ty
  case (arity, branch, branchType) of
    (1, Lambda q domain _, Pi _ _ result) => do
      result <- boundedResult position result
      motive <- unaryMotive position q domain result
      Right (BoxCase motive scrutinee branch)
    (2, Lambda q domain (Lambda r second _), Pi _ _ (Pi _ _ result)) => do
      result <- boundedResult position result
      motive <- binaryMotive position q r domain second result
      Right (PairCase motive scrutinee branch)
    _ => Left (CannotElaborate position "Record motive inference requires one or two typed pattern binders")

||| Infer a payload-independent result, comparing by bounded guarded conversion.
||| Dependent motives are handled separately from equation expected types.
||| The independent core checker still checks the resulting complete case.
dataBranchResult : Position -> Context n -> Maybe (Quantity, Term n) -> Term n -> Either ResolveError (Term n)
dataBranchResult position context descriptor branch = do
  ty <- case inferErased checkingDepth typeReductionFuel context branch of
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

constantDataResult : Position -> Context n -> List (Maybe (Quantity, Term n)) -> List (Term n) -> Either ResolveError (Term n)
constantDataResult position context [] [] = Left (CannotElaborate position "Cannot infer an empty data-case result")
constantDataResult position context (descriptor :: descriptors) (branch :: branches) = do
  first <- dataBranchResult position context descriptor branch
  agree first descriptors branches
  Right first
  where
    agree : Term n -> List (Maybe (Quantity, Term n)) -> List (Term n) -> Either ResolveError ()
    agree first [] [] = Right ()
    agree first (descriptor :: descriptors) (branch :: branches) = do
      result <- dataBranchResult position context descriptor branch
      if guardedEqual typeReductionFuel first result then agree first descriptors branches
        else Left (CannotElaborate position "Data-case branch results differ or guarded conversion was inconclusive; use an explicit return motive")
    agree first _ _ = Left (CannotElaborate position "Data-case branch count does not match shape")
constantDataResult position context _ _ = Left (CannotElaborate position "Data-case branch count does not match shape")

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

mutual
  ||| Visibility is accepted only on a checked module declaration's leading
  ||| erased prefix, followed by a source-authored ordinary Pi.
  public export
  elaborateSignature : List GlobalDefinition -> Maybe (Context n) -> Vect n String -> Expr -> Either ResolveError (Term n)
  elaborateSignature globals context env signature = elaborateSignatureWith False globals context env signature

  ||| Only generated declarations may have an implicit-only telescope, needed
  ||| for explicitly instantiated nullary data constructors.
  public export
  elaborateSignatureWith : Bool -> List GlobalDefinition -> Maybe (Context n) -> Vect n String -> Expr -> Either ResolveError (Term n)
  elaborateSignatureWith allowImplicitOnly globals context env (NImplicitPi span Erased name domain body) = do
    case body of
      NImplicitPi _ _ _ _ _ => Right ()
      NPi _ _ _ _ _ => Right ()
      _ => if allowImplicitOnly then Right () else Left (CannotElaborate span.start "Implicit prefix must be followed by an explicit Pi")
    domain <- elaborateInWith globals context env domain
    result <- elaborateSignatureWith allowImplicitOnly globals (map (\ctx => Extend ctx Erased domain) context) (name :: env) body
    Right (Pi Erased domain result)
  elaborateSignatureWith allowImplicitOnly globals context env (NImplicitPi span _ _ _ _) =
    Left (CannotElaborate span.start "Implicit binders must have quantity 0")
  elaborateSignatureWith allowImplicitOnly globals context env signature = elaborateInWith globals context env signature

  elaborateTerms : List GlobalDefinition -> Maybe (Context n) -> Vect n String -> List Expr -> Either ResolveError (List (Term n))
  elaborateTerms globals context env [] = Right []
  elaborateTerms globals context env (x :: xs) = [| elaborateInWith globals context env x :: elaborateTerms globals context env xs |]

  dataCaseTag : Position -> Term n -> Either ResolveError Nat
  dataCaseTag position value = case normalize typeReductionFuel value of
    OutOfFuel _ => Left (CannotElaborate position "Data-case constructor reduction budget exhausted")
    Normal (NominalValue _ (VariantValue _ tag Nothing)) => Right tag
    Normal (Lambda _ _ (NominalValue _ (VariantValue _ tag (Just (Variable FZ))))) => Right tag
    Normal _ => Left (CannotElaborate position "Data-case pattern must name a transparent nullary or unary constructor value")

  orderDataArms : Position -> Nat -> List (Maybe (Quantity, Term n)) -> List (Nat, Term n) -> Either ResolveError (List (Term n))
  orderDataArms position tag [] [] = Right []
  orderDataArms position tag [] _ = Left (CannotElaborate position "Unexpected data-case branch")
  orderDataArms position tag (_ :: rest) branches = do
    branch <- case lookup tag branches of Nothing => Left (CannotElaborate position "Missing data-case constructor"); Just body => Right body
    later <- orderDataArms position (S tag) rest (filter (\entry => fst entry /= tag) branches)
    Right (branch :: later)

  elaborateDataArms : List GlobalDefinition -> Context n -> Vect n String -> Term n -> Term n -> List (Term n) ->
                      List (Maybe (Quantity, Term n)) -> Maybe (Term n) -> List (Token, Maybe Token, Expr) -> Either ResolveError (List (Nat, Term n))
  elaborateDataArms globals ctx env nominal shape indices descriptors hint [] = Right []
  elaborateDataArms globals ctx env nominal shape indices descriptors hint ((name, binder, body) :: rest) = do
    if elem '.' (unpack name.spelling) then Right () else
      case lookupName name.spelling env of
        Just _ => Left (CannotElaborate name.span.start "Data-case constructor is shadowed by a local binder")
        Nothing => Right ()
    definition <- case find (\entry => entry.name == name.spelling) globals of
      Nothing => Left (Unbound name.span.start name.spelling)
      Just entry => Right entry
    if definition.quantity /= Unrestricted then Left (CannotElaborate name.span.start "Data-case constructor must be an unrestricted checked global") else Right ()
    if coreNodes definition.value > 512 then Left (CannotElaborate name.span.start "Data-case constructor exceeds 512 nodes") else Right ()
    let candidate = foldl Apply (rename absurd definition.value) indices
    tag <- dataCaseTag name.span.start candidate
    descriptor <- case variantAt tag descriptors of
      Nothing => Left (CannotElaborate name.span.start "Data-case constructor tag is outside the scrutinee shape")
      Just descriptor => Right descriptor
    expected <- case (descriptor, binder) of
      (Nothing, Nothing) => Right (NominalValue nominal (VariantValue shape tag Nothing))
      (Just (q, ty), Just _) =>
        Right (Lambda q ty (NominalValue (weaken nominal) (VariantValue (weaken shape) tag (Just (Variable FZ)))))
      _ => Left (CannotElaborate name.span.start "Data-case constructor payload arity does not match its branch")
    case betaCompare typeReductionFuel candidate expected of
      EqualNormalForms => Right ()
      DifferentNormalForms => Left (CannotElaborate name.span.start "Data-case constructor does not match the scrutinee type and shape")
      Inconclusive => Left (CannotElaborate name.span.start "Data-case constructor comparison budget exhausted")
    branch <- case (descriptor, binder) of
      (Nothing, Nothing) => case hint of
        Nothing => elaborateInWith globals (Just ctx) env body
        Just motive =>
          let applied = Apply motive (NominalValue nominal (VariantValue shape tag Nothing))
              result = fromMaybe applied (guardedNormal typeReductionFuel applied) in
            elaborateExpected globals ctx env result body
      (Just (q, ty), Just bound) => do
        result <- case hint of
          Nothing => elaborateInWith globals (Just (Extend ctx q ty)) (bound.spelling :: env) body
          Just motive =>
            let value = NominalValue (weaken nominal) (VariantValue (weaken shape) tag (Just (Variable FZ)))
                applied = Apply (weaken motive) value
                expectedResult = fromMaybe applied (guardedNormal typeReductionFuel applied) in
              elaborateExpected globals (Extend ctx q ty) (bound.spelling :: env) expectedResult body
        Right (Lambda q ty result)
      _ => Left (CannotElaborate name.span.start "Invalid data-case payload branch")
    following <- elaborateDataArms globals ctx env nominal shape indices descriptors hint rest
    if any (\entry => fst entry == tag) following
       then Left (CannotElaborate name.span.start "Duplicate data-case constructor") else Right ()
    Right ((tag, branch) :: following)

  -- A result type is available here only for a direct equation body. The
  -- variable abstraction is a renaming, so it cannot duplicate subtrees.
  public export
  elaborateExpected : List GlobalDefinition -> Context n -> Vect n String -> Term n -> Expr -> Either ResolveError (Term n)
  elaborateExpected globals context env expected expression@(NApply span function argument) =
    if hasImplicitCall globals env expression
      then elaborateImplicitCall globals context env (Just expected) expression
      else do
        resolved <- elaborateInWith globals (Just context) env function
        elaborateApplication globals (Just context) env resolved argument
  elaborateExpected globals context env expected expression@(NImplicitApply span _ _) =
    elaborateImplicitCall globals context env (Just expected) expression
  elaborateExpected globals context env expected (NDataCase span value Nothing arms) =
    elaborateDataCase globals context env span value Nothing arms (Just expected)
  elaborateExpected globals context env (Pi _ _ expected) (NLambda span q name domain body) = do
    domain <- elaborateInWith globals (Just context) env domain
    body <- elaborateExpected globals (Extend context q domain) (name :: env) expected body
    Right (Lambda q domain body)
  elaborateExpected globals context env expected (NUnitCase span scrutinee body) = do
    scrutinee <- elaborateInWith globals (Just context) env scrutinee
    body <- elaborateExpected globals context env expected body
    Right (UnitCase scrutinee body)
  elaborateExpected globals context env expected (NIf span condition yes no) = do
    condition <- elaborateInWith globals (Just context) env condition
    yes <- elaborateExpected globals context env expected yes
    no <- elaborateExpected globals context env expected no
    Right (BoolCase condition yes no)
  elaborateExpected globals context env expected expression@(NLet span q name annotation value body) =
    if not (wantsExpected body || hasImplicitCall globals (name :: env) body) || typeNodes expected > inferredResultNodes
      then elaborateInWith globals (Just context) env expression else do
      ty <- elaborateInWith globals (Just context) env annotation
      value <- elaborateExpected globals context env ty value
      body <- elaborateExpected globals (Extend context q ty) (name :: env) (weaken expected) body
      Right (Apply (Lambda q ty body) value)
  elaborateExpected globals context env expected body = elaborateInWith globals (Just context) env body

  -- Try the authored scrutinee first to preserve exact-abstraction behavior.
  -- Only a fully admitted guarded normalization may supply a second proposal;
  -- both candidates are checked against the original, unnormalized result.
  chooseExpectedMotive : Position -> Context n -> Term n -> Term n -> Term n -> Term n -> List (Term n) -> Either ResolveError (Term n)
  chooseExpectedMotive position ctx nominal shape scrutinee result branches = do
    exact <- expectedDataMotive position nominal result scrutinee
    let candidate = assembleDataCase nominal shape exact scrutinee branches
    case checkErased checkingDepth typeReductionFuel ctx candidate result of
      Right () => Right exact
      Left _ => case guardedNormal typeReductionFuel scrutinee of
        Nothing => Right exact
        Just normal => if sameSyntax normal scrutinee then Right exact else
          case expectedDataMotive position nominal result normal of
            Left _ => Right exact
            Right converted =>
              let alternative = assembleDataCase nominal shape converted scrutinee branches in
                case checkErased checkingDepth typeReductionFuel ctx alternative result of
                  Right () => Right converted
                  Left _ => Right exact

  elaborateDataCase : List GlobalDefinition -> Context n -> Vect n String -> SourceSpan -> Expr -> Maybe Expr -> List (Token, Maybe Token, Expr) -> Maybe (Term n) -> Either ResolveError (Term n)
  elaborateDataCase globals ctx env span value motive arms expected = do
    let context = Just ctx
    scrutinee <- elaborateInWith globals context env value
    inferred <- case inferErased checkingDepth typeReductionFuel ctx scrutinee of
      Left err => Left (CannotElaborate span.start ("Cannot infer data-case scrutinee: " ++ show err))
      Right ty => Right ty
    nominal <- the (Either ResolveError (Term n)) $ case weakHead typeReductionFuel inferred of
      HeadForm term@(NominalType _ _ _) => Right term
      HeadLimit _ => Left (CannotElaborate span.start "Data-case scrutinee reduction budget exhausted")
      _ => Left (CannotElaborate span.start "Data case requires a nonrecursive nominal data scrutinee")
    if coreNodes nominal > 512 then Left (CannotElaborate span.start "Data-case nominal type exceeds 512 nodes") else Right ()
    shape <- the (Either ResolveError (Term n)) $ case nominal of
      NominalType _ _ shape => case weakHead typeReductionFuel shape of
        HeadForm shape@(VariantType _) => Right shape
        HeadLimit _ => Left (CannotElaborate span.start "Data-case shape reduction budget exhausted")
        _ => Left (CannotElaborate span.start "Data-case nominal shape is not a variant")
      _ => Left (CannotElaborate span.start "Invalid data-case nominal type")
    case shape of
      VariantType descriptors => do
        if length descriptors > 64 then Left (CannotElaborate span.start "Data-case branch admission exhausted (64)") else Right ()
        let indices = case nominal of NominalType _ args _ => args; _ => []
        explicit <- the (Either ResolveError (Maybe (Term n))) $ case motive of
          Just authored => Just <$> elaborateInWith globals context env authored
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
        checked <- elaborateDataArms globals ctx env nominal shape indices descriptors boundedHint arms
        ordered <- orderDataArms span.start 0 descriptors checked
        selected <- case explicit of
          Just authored => Right authored
          Nothing => case (expected, scrutinee) of
            (Just result, _) =>
              -- Retain a previously accepted constant motive only if it also
              -- checks against this expected type. This probe is erased-only;
              -- the completed declaration is independently checked again. Do
              -- not impose the abstraction size limit on the constant path.
              case constantDataResult span.start ctx descriptors ordered of
                Right common =>
                  let constant = Lambda Erased nominal (weaken common)
                      candidate = assembleDataCase nominal shape constant scrutinee ordered in
                    case checkErased checkingDepth typeReductionFuel ctx candidate result of
                      Right () => Right constant
                      Left _ => chooseExpectedMotive span.start ctx nominal shape scrutinee result ordered
                Left _ => chooseExpectedMotive span.start ctx nominal shape scrutinee result ordered
            _ => do
              result <- constantDataResult span.start ctx descriptors ordered
              Right (Lambda Erased nominal (weaken result))
        Right (assembleDataCase nominal shape selected scrutinee ordered)
      _ => Left (CannotElaborate span.start "Invalid data-case shape")

  equationBody : List GlobalDefinition -> Context n -> Vect n String -> Term n -> List Token -> Expr -> Either ResolveError (Term n)
  equationBody globals context env expected [] body = elaborateExpected globals context env expected body
  equationBody globals context env expected (name :: rest) body = do
    -- Do not reduce an unchecked signature to expose Pi: head beta reduction
    -- can expand before any post-reduction node bound. Explicit Pi syntax is
    -- the deliberately narrower, pre-clone-accounted first slice.
    case expected of
      Pi q domain result => do
        if coreNodes domain > 512 then Left (CannotElaborate name.span.start "Function equation parameter type exceeds 512 nodes") else Right ()
        following <- equationBody globals (Extend context q domain) (name.spelling :: env) result rest body
        Right (Lambda q domain following)
      _ => Left (CannotElaborate name.span.start "Function equation requires an explicit Pi for every named parameter")

  elaborateArms : List GlobalDefinition -> Maybe (Context n) -> Vect n String -> List (Maybe (Quantity, Expr)) -> Either ResolveError (List (Maybe (Quantity, Term n)))
  elaborateArms globals context env [] = Right []
  elaborateArms globals context env (Nothing :: xs) = (Nothing ::) <$> elaborateArms globals context env xs
  elaborateArms globals context env (Just (q, ty) :: xs) = do
    ty <- elaborateInWith globals context env ty
    rest <- elaborateArms globals context env xs
    Right (Just (q, ty) :: rest)

  ||| Resolve with newest-first names. Binder domains see the old environment;
  ||| bodies see the new binder. Shadowing resolves to the nearest binder.
  ||| Underscore is a wildcard and cannot be referenced.
  public export
  elaborateInWith : List GlobalDefinition -> Maybe (Context n) -> Vect n String -> Expr -> Either ResolveError (Term n)
  elaborateInWith globals context env (NRef span name) =
    if name == "_" then Left (Unbound span.start name)
       else case lookupName name env of
         Nothing => case lookupGlobal name globals of
           Nothing => Left (Unbound span.start name)
           Just value => Right (rename absurd value)
         Just index => Right (Variable index)
  elaborateInWith globals context env (NQualifiedRef span name) =
    case lookupGlobal name globals of
      Nothing => Left (Unbound span.start name)
      Just value => Right (rename absurd value)
  elaborateInWith globals context env (NSort span level) = Right (Universe level)
  elaborateInWith globals context env (NUnitType span) = Right UnitType
  elaborateInWith globals context env (NUnitValue span) = Right UnitValue
  elaborateInWith globals context env (NStringType span) = Right StringType
  elaborateInWith globals context env (NStringValue span value) = Right (StringValue value)
  elaborateInWith globals context env (NBoolType span) = Right BoolType
  elaborateInWith globals context env (NBoolValue span True) = Right BoolTrue
  elaborateInWith globals context env (NBoolValue span False) = Right BoolFalse
  elaborateInWith globals context env (NIf span condition yes no) =
    [| BoolCase (elaborateInWith globals context env condition) (elaborateInWith globals context env yes) (elaborateInWith globals context env no) |]
  elaborateInWith globals context env (NUnitCase span scrutinee body) =
    [| UnitCase (elaborateInWith globals context env scrutinee) (elaborateInWith globals context env body) |]
  elaborateInWith globals context env (NSigma span q r name domain body) = do
    domain <- elaborateInWith globals context env domain
    body <- elaborateInWith globals (map (\ctx => Extend ctx q domain) context) (name :: env) body
    Right (Sigma q r domain body)
  elaborateInWith globals context env (NPairValue span ty first second) =
    [| PairValue (elaborateInWith globals context env ty) (elaborateInWith globals context env first) (elaborateInWith globals context env second) |]
  elaborateInWith globals context env (NNominalType span key indices shape) = do
    indices <- elaborateTerms globals context env indices
    shape <- elaborateInWith globals context env shape
    if mentionsNominal key shape then Left (CannotElaborate span.start "Recursive data is not supported") else Right ()
    Right (NominalType key indices shape)
  elaborateInWith globals context env (NNominalValue _ ty value) = [| NominalValue (elaborateInWith globals context env ty) (elaborateInWith globals context env value) |]
  elaborateInWith globals context env (NNominalCase _ motive value branch) = [| NominalCase (elaborateInWith globals context env motive) (elaborateInWith globals context env value) (elaborateInWith globals context env branch) |]
  elaborateInWith globals context env (NVariantType _ arms) = VariantType <$> elaborateArms globals context env arms
  elaborateInWith globals context env (NVariantValue _ ty tag Nothing) = (\t => VariantValue t tag Nothing) <$> elaborateInWith globals context env ty
  elaborateInWith globals context env (NVariantValue _ ty tag (Just value)) = [| VariantValue (elaborateInWith globals context env ty) (pure tag) (Just <$> elaborateInWith globals context env value) |]
  elaborateInWith globals context env (NVariantCase _ motive value branches) = [| VariantCase (elaborateInWith globals context env motive) (elaborateInWith globals context env value) (elaborateTerms globals context env branches) |]
  elaborateInWith globals context env (NBoxType span q ty) = [| BoxType (pure q) (elaborateInWith globals context env ty) |]
  elaborateInWith globals context env (NBoxValue span ty value) = [| BoxValue (elaborateInWith globals context env ty) (elaborateInWith globals context env value) |]
  elaborateInWith globals context env (NBoxCase span motive value branch) =
    [| BoxCase (elaborateInWith globals context env motive) (elaborateInWith globals context env value) (elaborateInWith globals context env branch) |]
  elaborateInWith globals context env (NDataCase span value motive arms) = do
    ctx <- case context of Nothing => Left (CannotElaborate span.start "Data case requires a typed context"); Just ctx => Right ctx
    elaborateDataCase globals ctx env span value motive arms Nothing
  elaborateInWith globals context env (NEquationLambda span names signature body) = do
    ctx <- case context of Nothing => Left (CannotElaborate span.start "Function equations require a typed context"); Just ctx => Right ctx
    expected <- elaborateSignature globals context env signature
    equationBody globals ctx env expected names body
  elaborateInWith globals context env (NPatternLambda span _ _) =
    Left (CannotElaborate span.start "Inferred field binders require a constructor-named pattern")
  elaborateInWith globals context env (NConstructorCase span arity constructor scrutinee branch motive) = do
    if not (namedConstructor constructor)
       then Left (CannotElaborate (extent constructor).start "Pattern constructor must be a named function, optionally explicitly instantiated") else Right ()
    typedContext <- case context of
      Nothing => Left (CannotElaborate span.start "Named pattern checking requires a typed context")
      Just ctx => Right ctx
    candidate <- elaborateInWith globals context env constructor
    value <- elaborateInWith globals context env scrutinee
    named <- instantiateParameters (extent constructor).start arity typedContext candidate value
    branch <- elaboratePatternBranch globals typedContext env (extent constructor).start arity named branch
    case motive of
      Nothing => inferCase span.start arity typedContext value branch
      Just authored => do
        explicit <- elaborateInWith globals context env authored
        Right (if arity == 1 then BoxCase explicit value branch else PairCase explicit value branch)
  elaborateInWith globals context env (NInferCase span arity scrutinee branch) = do
    typedContext <- case context of
      Nothing => Left (CannotElaborate span.start "Motive inference requires a typed context; use contextual expression elaboration")
      Just ctx => Right ctx
    value <- elaborateInWith globals context env scrutinee
    branch <- elaborateInWith globals context env branch
    inferCase span.start arity typedContext value branch
  elaborateInWith globals context env (NPairCase span motive value branch) =
    [| PairCase (elaborateInWith globals context env motive) (elaborateInWith globals context env value) (elaborateInWith globals context env branch) |]
  elaborateInWith globals context env (NImplicitPi span _ _ _ _) =
    Left (CannotElaborate span.start "Implicit binders are supported only as the leading binder of a module declaration signature")
  elaborateInWith globals context env (NConstraintPi span q name domain body) = do
    domain <- elaborateInWith globals context env domain
    constraintType span.start q domain
    body <- elaborateInWith globals (map (\ctx => Extend ctx q domain) context) (name :: env) body
    Right (Pi q domain body)
  elaborateInWith globals context env (NImplementationApply span origin function) = do
    typed <- case context of
      Nothing => Left (CannotElaborate origin.start "Implementation lookup requires a typed context")
      Just ctx => Right ctx
    function <- elaborateInWith globals context env function
    selectImplementation origin.start globals typed function
  elaborateInWith globals context env (NDictionaryApply span origin function argument) = do
    typed <- case context of
      Nothing => Left (CannotElaborate origin.start "Dictionary selection requires a typed context")
      Just ctx => Right ctx
    function <- elaborateInWith globals context env function
    argument <- case argument of
      Nothing => Right Nothing
      Just value => Just <$> elaborateInWith globals context env value
    selectDictionary origin.start typed env function argument
  elaborateInWith globals context env (NPi span q name domain body) = do
    domain <- elaborateInWith globals context env domain
    body <- elaborateInWith globals (map (\ctx => Extend ctx q domain) context) (name :: env) body
    Right (Pi q domain body)
  elaborateInWith globals context env (NLambda span q name domain body) = do
    domain <- elaborateInWith globals context env domain
    body <- elaborateInWith globals (map (\ctx => Extend ctx q domain) context) (name :: env) body
    Right (Lambda q domain body)
  elaborateInWith globals context env (NInfix span function left right) = do
    operator <- elaborateInWith globals context env function
    first <- elaborateApplication globals context env operator left
    elaborateApplication globals context env first right
  elaborateInWith globals context env expression@(NApply span sourceFunction argument) =
    if hasImplicitCall globals env expression then do
      ctx <- case context of
        Nothing => Left (CannotElaborate span.start "Implicit insertion requires a typed context; use explicit {arguments}")
        Just ctx => Right ctx
      elaborateImplicitCall globals ctx env Nothing expression
    else do
      function <- elaborateInWith globals context env sourceFunction
      elaborateApplication globals context env function argument
  elaborateInWith globals context env expression@(NImplicitApply span sourceFunction argument) = do
    ctx <- case context of
      Nothing => Left (CannotElaborate span.start "Explicit {arguments} require a typed context")
      Just ctx => Right ctx
    elaborateImplicitCall globals ctx env Nothing expression

  elaborateInWith globals context env (NSequence span first rest) = do
    action <- elaborateInWith globals context env first
    following <- elaborateInWith globals context env rest
    Right (IOBind UnitType UnitType action
      (Lambda Linear UnitType (UnitCase (Variable FZ) (weaken following))))
  elaborateInWith globals context env (NDoBind span name domain action body) = do
    ty <- elaborateInWith globals context env domain
    action <- elaborateInWith globals context env action
    body <- elaborateInWith globals (map (\ctx => Extend ctx Linear ty) context) (name :: env) body
    Right (IOBind ty UnitType action (Lambda Linear ty body))
  -- Checking an identity application enforces the expected domain using existing
  -- typing/compatibility rules. Linear use preserves the term's runtime usage.
  elaborateInWith globals context env (NAscribe span term expected) = do
    ty <- elaborateInWith globals context env expected
    term <- case context of
      Just ctx => elaborateExpected globals ctx env ty term
      Nothing => elaborateInWith globals context env term
    Right (Apply (Lambda Linear ty (Variable FZ)) term)

  -- The binding is nonrecursive: annotation and value use the outer environment.
  -- A lambda/application enforces the annotation and declared resource quantity.
  elaborateInWith globals context env (NLet span q name expected value body) = do
    ty <- elaborateInWith globals context env expected
    value <- case context of
      Just ctx => elaborateExpected globals ctx env ty value
      Nothing => elaborateInWith globals context env value
    body <- elaborateInWith globals (map (\ctx => Extend ctx q ty) context) (name :: env) body
    Right (Apply (Lambda q ty body) value)

  elaborateInWith globals context env (NDoResult span result body) = do
    ty <- elaborateInWith globals context env result
    value <- elaborateDo globals context env ty body
    Right (Apply (Lambda Linear (IOType ty) (Variable FZ)) value)

  -- Traverse the authored spine structurally. Arguments are elaborated only
  -- as direct source subexpressions, preserving totality and source order.
  collectImplicitCall : List GlobalDefinition -> Context n -> Vect n String -> Expr -> Either ResolveError (PendingImplicit n)
  collectImplicitCall globals context env (NImplicitApply span function argument) = do
    pending <- collectImplicitCall globals context env function
    if not (null pending.ordinary) || isJust pending.applied
      then Left (CannotElaborate span.start "Explicit {arguments} must precede ordinary arguments") else Right ()
    if length pending.given >= pending.entry.implicitPrefix
      then Left (CannotElaborate span.start "Too many explicit {arguments}") else Right ()
    value <- elaborateInWith globals (Just context) env argument
    Right ({ given := pending.given ++ [value] } pending)
  collectImplicitCall globals context env (NApply span function argument) = do
    pending <- collectImplicitCall globals context env function
    case pending.applied of
      Just function => do
        result <- elaborateApplication globals (Just context) env function argument
        Right ({ applied := Just result } pending)
      Nothing => if length pending.given == pending.entry.implicitPrefix then do
          result <- elaborateApplication globals (Just context) env (foldl Apply pending.function pending.given) argument
          Right ({ applied := Just result } pending)
        else do
          if length pending.ordinary >= implicitTelescopeLimit
            then Left (CannotElaborate span.start "Implicit inference telescope admission exhausted (64)") else Right ()
          value <- elaborateInWith globals (Just context) env argument
          proposed <- implicitArgumentType span.start implicitProposalDepth context value
          state <- case pending.solver of
            Just state => Right state
            Nothing => beginImplicit span.start pending.entry.implicitPrefix
                         (rename absurd pending.entry.declaredType) pending.given
          state <- advanceImplicit span.start state proposed
          let values = pending.ordinary ++ [value]
          if implicitSolved state then do
            inferred <- finishImplicit span.start context state Nothing
            Right ({ applied := Just (foldl Apply (foldl Apply pending.function inferred) values), ordinary := [], solver := Nothing } pending)
            else Right ({ ordinary := values, solver := Just state } pending)
  collectImplicitCall globals context env head = do
    entry <- case implicitHead globals env head of
      Nothing => Left (CannotElaborate (extent head).start "Explicit {arguments} require a direct global with an implicit prefix")
      Just entry => Right entry
    value <- case lookupGlobal entry.name globals of
      Nothing => Left (CannotElaborate (extent head).start "Implicit global is unavailable")
      Just value => Right (rename absurd value)
    Right (PendingCall entry value [] [] Nothing Nothing)

  elaborateImplicitCall : List GlobalDefinition -> Context n -> Vect n String -> Maybe (Term n) -> Expr -> Either ResolveError (Term n)
  elaborateImplicitCall globals context env expected source = do
    let (head, args) = applicationSpine source
    entry <- case implicitHead globals env head of
      Nothing => Left (CannotElaborate (extent source).start "Explicit {arguments} require a direct global with an implicit prefix")
      Just entry => Right entry
    if entry.implicitPrefix > implicitTelescopeLimit
      then Left (CannotElaborate (extent source).start "Implicit telescope admission exhausted (64)") else Right ()
    needsInference <- spineAdmission (extent source).start entry.implicitPrefix args
    if needsInference && typeNodes entry.declaredType > inferredParameterNodes
      then Left (CannotElaborate (extent source).start "Implicit function type exceeds 512 nodes; use explicit {arguments}") else Right ()
    if needsInference && payloadSize entry.declaredType > payloadLimit
      then Left (CannotElaborate (extent source).start "Implicit function type exceeds payload admission; use explicit {arguments}") else Right ()
    pending <- collectImplicitCall globals context env source
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
          inferred <- finishImplicit (extent source).start context state expected
          Right (foldl Apply (foldl Apply pending.function inferred) pending.ordinary)

  elaborateApplication : List GlobalDefinition -> Maybe (Context n) -> Vect n String -> Term n -> Expr -> Either ResolveError (Term n)
  elaborateApplication globals context env function argument = do
    argument <- case context of
      Just ctx => if wantsExpected argument || hasImplicitCall globals env argument then
        case inferErased checkingDepth typeReductionFuel ctx function of
          Right (Pi _ domain _) =>
            if typeNodes domain <= inferredResultNodes
              then elaborateExpected globals ctx env domain argument
              else elaborateInWith globals context env argument
          _ => elaborateInWith globals context env argument
        else elaborateInWith globals context env argument
      Nothing => elaborateInWith globals context env argument
    Right (Apply function argument)

  elaboratePatternBranch : List GlobalDefinition -> Context n -> Vect n String -> Position ->
                           Nat -> Term n -> Expr -> Either ResolveError (Term n)
  elaboratePatternBranch globals context env position arity constructor (NPatternLambda span names body) = do
    fields <- inferConstructorFields position arity context constructor
    case (fields, names) of
      (OneField q domain, [name]) => do
        body <- elaborateInWith globals (Just (Extend context q domain)) (name.spelling :: env) body
        Right (Lambda q domain body)
      (TwoFields q domain r second, [first, last]) => do
        body <- elaborateInWith globals (Just (Extend (Extend context q domain) r second))
                  (last.spelling :: first.spelling :: env) body
        Right (Lambda q domain (Lambda r second body))
      _ => Left (CannotElaborate span.start "Constructor field count does not match the pattern names")
  elaboratePatternBranch globals context env position arity constructor branch = do
    resolved <- elaborateInWith globals (Just context) env branch
    checkConstructor position arity context constructor resolved
    Right resolved

  -- The block result is resolved outside its statements and weakened under each
  -- local binder. It must never be re-resolved under a shadowing statement name.
  elaborateDo : List GlobalDefinition -> Maybe (Context n) -> Vect n String -> Term n -> Expr ->
              Either ResolveError (Term n)
  elaborateDo globals context env result (NSequence span first rest) = do
    action <- elaborateInWith globals context env first
    following <- elaborateDo globals context env result rest
    Right (IOBind UnitType result action
      (Lambda Linear UnitType (UnitCase (Variable FZ) (weaken following))))
  elaborateDo globals context env result (NDoBind span name domain action body) = do
    ty <- elaborateInWith globals context env domain
    action <- elaborateInWith globals context env action
    body <- elaborateDo globals (map (\ctx => Extend ctx Linear ty) context) (name :: env) (weaken result) body
    Right (IOBind ty result action (Lambda Linear ty body))
  elaborateDo globals context env result (NLet span q name expected value body) = do
    ty <- elaborateInWith globals context env expected
    value <- case context of
      Just ctx => elaborateExpected globals ctx env ty value
      Nothing => elaborateInWith globals context env value
    body <- elaborateDo globals (map (\ctx => Extend ctx q ty) context) (name :: env) (weaken result) body
    Right (Apply (Lambda q ty body) value)
  elaborateDo globals context env result term = case context of
    Just ctx => elaborateExpected globals ctx env (IOType result) term
    Nothing => elaborateInWith globals context env term

||| Contextual elaboration of a closed source expression.
public export
elaborateClosedWith : List GlobalDefinition -> Expr -> Either ResolveError (Term 0)
elaborateClosedWith globals = elaborateInWith globals (Just Empty) []

public export
elaborateClosed : Expr -> Either ResolveError (Term 0)
elaborateClosed = elaborateClosedWith []
