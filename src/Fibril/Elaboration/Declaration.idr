-- Explicit record lowering and admission; generated IR still needs core checking.
module Fibril.Elaboration.Declaration

import Data.List
import Data.String
import Data.List1
import Data.Maybe
import Fibril.Elaboration.Data
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Declaration.Syntax
import Fibril.Elaboration.Interface

%default total

public export
record ElaborationError where
  constructor ElaborationFailure
  position : Position
  message : String

public export
Show ElaborationError where
  show err = show err.position ++ ": " ++ err.message

qualifiedMatches : String -> List String -> List String
qualifiedMatches target [] = []
qualifiedMatches target (name :: rest) =
  let following = qualifiedMatches target rest in
  case reverse (forget (Data.String.split (== '.') name)) of
    short :: _ :: _ => if short == target then name :: following else following
    _ => following

-- General mutual groups -------------------------------------------------------------
-- A `mutual where` block that is not the bounded two-member Nat/Bool form is rewritten
-- into ordinary declarations that the usual checker, size-change gate and evaluator
-- already handle:
--
--   * one hidden dispatcher  mutual(f,g,..) : (tag : String) -> <shared signature>  whose
--     parameters are the tag followed by the members' shared parameters. A chain of ifs
--     compares the tag with each member's name (a string tag keeps the elaboration-size
--     estimate linear; nested case expressions multiply it); each arm binds every member's
--     name with a let to the dispatcher applied to that member's tag, renames the shared
--     parameters to the member's own, and runs the member's body;
--   * each member, defined as the dispatcher applied to its tag.
--
-- All members share one signature. Termination is the ordinary size-change check on the
-- dispatcher, so every call in the group must itself make some argument smaller.

piBinders : Expr -> List (Quantity, String, Expr)
piBinders (NPi _ q name domain codomain) = (q, name, domain) :: piBinders codomain
piBinders _ = []

piResult : Expr -> Expr
piResult (NPi _ _ _ _ codomain) = piResult codomain
piResult other = other

-- The bounded form is exactly two members whose parameters are Nat or Bool (at least one
-- Nat) and whose result is Bool. It keeps its dedicated, verified lowering.
boundedNatBoolShape : Expr -> Bool
boundedNatBoolShape signature =
  let binders = piBinders signature
      domains = map (\(_, _, domain) => domain) binders
      isNat : Expr -> Bool
      isNat (NRef _ "Nat") = True
      isNat _ = False
      isBool : Expr -> Bool
      isBool (NBoolType _) = True
      isBool _ = False
      resultIsBool = isBool (piResult signature)
   in (length binders == 1 || length binders == 2) && resultIsBool && any isNat domains &&
      all (\domain => isNat domain || isBool domain) domains

-- The dedicated forwarding-alias slice only understands linear (Nat, Bool) or (Bool, Nat)
-- signatures. An alias with any other signature is an ordinary member of a general group.
forwardingSignature : Expr -> Bool
forwardingSignature (NPi _ Linear _ (NRef _ "Nat") (NPi _ Linear _ (NBoolType _) (NBoolType _))) = True
forwardingSignature (NPi _ Linear _ (NBoolType _) (NPi _ Linear _ (NRef _ "Nat") (NBoolType _))) = True
forwardingSignature _ = False

isForwardingEquation : Expr -> Bool
isForwardingEquation (NEquationLambda _ _ _ (NApply _ _ _)) = True
isForwardingEquation _ = False

public export
boundedNatBoolGroup : MutualDeclaration -> Bool
boundedNatBoolGroup group =
  null group.others && boundedNatBoolShape group.first.expected && boundedNatBoolShape group.second.expected &&
  (not (isForwardingEquation group.first.value || isForwardingEquation group.second.value) ||
   (forwardingSignature group.first.expected && forwardingSignature group.second.expected))

-- if tag == "f" then <f's arm> else if tag == "g" then ... else <last arm>. The last arm is
-- reached for the last member's tag, the only tag left; the tags are the member names.
dispatchTree : SourceSpan -> String -> List (String, Expr) -> Maybe Expr
dispatchTree span scrutinee [] = Nothing
dispatchTree span scrutinee [(_, arm)] = Just arm
dispatchTree span scrutinee ((name, arm) :: rest) =
  let sameTag = NApply span (NApply span (NRef span "primStringEqual") (NRef span scrutinee)) (NStringValue span name)
   in map (\other => NIf span sameTag arm other) (dispatchTree span scrutinee rest)

-- let (q name : domain) = $p<index> in body, for each shared parameter, outermost first.
renameParameters : SourceSpan -> Nat -> List (Quantity, String, Expr) -> Expr -> Expr
renameParameters span index [] body = body
renameParameters span index ((q, name, domain) :: rest) body =
  NLet span q name domain (NRef span ("$p" ++ show index)) (renameParameters span (S index) rest body)

memberNamesLets : SourceSpan -> String -> List Declaration -> Expr -> Expr
memberNamesLets span dispatcher [] body = body
memberNamesLets span dispatcher (member :: rest) body =
  NLet span Unrestricted member.name member.expected
       (NApply span (NRef span dispatcher) (NStringValue span member.name))
       (memberNamesLets span dispatcher rest body)

memberEquation : Declaration -> Either ElaborationError (List Token, Expr)
memberEquation decl = case decl.value of
  NEquationLambda _ names _ body => Right (names, body)
  _ => Left (ElaborationFailure decl.nameSpan.start
        "General mutual members must be written as function equations (f x = ...)")

-- A member is the dispatcher applied to its tag; it keeps its authored signature and spans.
memberDefinition : String -> Bool -> Declaration -> Declaration
memberDefinition dispatcher exported member =
  Defined member.span member.nameSpan member.definitionNameSpan exported member.quantity member.name member.expected
    (NApply member.span (NRef member.span dispatcher) (NStringValue member.span member.name))

public export
generalMutual : MutualDeclaration -> Either ElaborationError (List Declaration)
generalMutual group = do
  let members = group.first :: group.second :: group.others
  let names = map name members
  let span = group.span
  if length (nub names) /= length names
    then Left (ElaborationFailure group.first.nameSpan.start "Mutual members need distinct names") else Right ()
  case find (\member => member.quantity /= Unrestricted || member.dictionary || member.generated ||
                        elem member.name ["_", "Nat", "Zero", "Succ"]) members of
    Just member => Left (ElaborationFailure member.nameSpan.start "Mutual members need unrestricted ordinary names")
    Nothing => Right ()
  equations <- traverse memberEquation members
  let arity = length (piBinders group.first.expected)
  case find (\(member, parts) => length (fst parts) /= arity || length (piBinders member.expected) /= arity)
            (zip members equations) of
    Just (member, _) => Left (ElaborationFailure member.nameSpan.start
      "Mutual members must take the same number of arguments, each named in the equation")
    Nothing => Right ()
  case find (\(member, parts) =>
               any (\((_, binderName, _), token) => binderName /= token.spelling)
                   (zip (piBinders member.expected) (fst parts)))
            (zip members equations) of
    Just (member, _) => Left (ElaborationFailure member.nameSpan.start
      "Mutual members must name their parameters as their signature does")
    Nothing => Right ()
  let dispatcher = "mutual(" ++ concat (intersperse "," names) ++ ")"
  let tagToken = Located Name "$tag" span
  let parameterTokens = map (\index => Located Name ("$p" ++ show index) span) (take arity [1, 2, 3, 4, 5, 6, 7, 8])
  let dispatcherSignature = NPi span Unrestricted "$tag" (NStringType span) group.first.expected
  let arms = map (\(member, parts) =>
                    (member.name, memberNamesLets span dispatcher members
                      (renameParameters span 1 (piBinders member.expected) (snd parts))))
                 (zip members equations)
  case dispatchTree span "$tag" arms of
    Nothing => Left (ElaborationFailure group.first.nameSpan.start "Mutual groups need at least two members")
    Just tree =>
      let body = NEquationLambda span (tagToken :: parameterTokens) dispatcherSignature tree
          dispatcherDecl = Declared True span group.first.nameSpan group.first.definitionNameSpan False
                             Unrestricted dispatcher dispatcherSignature body
       in Right (dispatcherDecl :: map (memberDefinition dispatcher group.exported) members)

mutual
  fieldPis : SourceSpan -> List RecordField -> Expr -> Expr
  fieldPis region [] body = body
  fieldPis region (field :: rest) body =
    NPi region field.quantity field.token.spelling field.ty (fieldPis region rest body)

  fieldLambdas : SourceSpan -> List RecordField -> Expr -> Expr
  fieldLambdas region [] body = body
  fieldLambdas region (field :: rest) body =
    NLambda region field.quantity field.token.spelling field.ty (fieldLambdas region rest body)

  parameterPis : SourceSpan -> List RecordParameter -> Expr -> Expr
  parameterPis region [] body = body
  parameterPis region (parameter :: rest) body =
    NPi region Erased parameter.name parameter.domain (parameterPis region rest body)

  constructorParameterPis : Bool -> SourceSpan -> List RecordParameter -> Expr -> Expr
  constructorParameterPis False region params body = parameterPis region params body
  constructorParameterPis True region [] body = body
  constructorParameterPis True region (parameter :: rest) body =
    NImplicitPi region Erased parameter.name parameter.domain (constructorParameterPis True region rest body)

  parameterLambdas : SourceSpan -> List RecordParameter -> Expr -> Expr
  parameterLambdas region [] body = body
  parameterLambdas region (parameter :: rest) body =
    NLambda region Erased parameter.name parameter.domain (parameterLambdas region rest body)

  applyParameters : SourceSpan -> Expr -> List RecordParameter -> Expr
  applyParameters region function [] = function
  applyParameters region function (parameter :: rest) =
    applyParameters region (NApply region function (NRef parameter.span parameter.name)) rest

  applyConstructorParameters : Bool -> SourceSpan -> Expr -> List RecordParameter -> Expr
  applyConstructorParameters False region function params = applyParameters region function params
  applyConstructorParameters True region function [] = function
  applyConstructorParameters True region function (parameter :: rest) =
    applyConstructorParameters True region (NImplicitApply region function (NRef parameter.span parameter.name)) rest

  fieldRef : RecordField -> Expr
  fieldRef field = NRef field.token.span field.token.spelling

  -- Preserve the historical two-field representation exactly. Wider records
  -- consume their right-nested tail once. Singleton records use a unary box.
  recordType : SourceSpan -> List RecordField -> Expr
  recordType region [] = NUnitType region
  recordType region [field] = NBoxType region field.quantity field.ty
  recordType region [first, second] = NSigma region first.quantity second.quantity first.token.spelling first.ty second.ty
  recordType region (first :: rest) = NSigma region first.quantity Linear first.token.spelling first.ty (recordType region rest)

  recordValue : SourceSpan -> List RecordField -> Expr
  recordValue region [] = NUnitValue region
  recordValue region [field] = NBoxValue region (recordType region [field]) (fieldRef field)
  recordValue region [first, second] = NPairValue region (recordType region [first, second]) (fieldRef first) (fieldRef second)
  recordValue region fields@(first :: rest) =
    NPairValue region (recordType region fields) (fieldRef first) (recordValue region rest)

  applyFields : SourceSpan -> Expr -> List RecordField -> Expr
  applyFields region function [] = function
  applyFields region function (field :: rest) = applyFields region (NApply region function (fieldRef field)) rest

  -- Every recursive tail elimination has an explicit motive rebuilding the
  -- enclosing pair. No eta rule, resource coercion, or unchecked core is needed.
  consume : SourceSpan -> List RecordField -> Expr -> Expr -> Expr -> Expr
  consume region [] motive value branch = branch
  consume region [field] motive value branch = NBoxCase region motive value branch
  consume region [first, second] motive value branch = NPairCase region motive value branch
  consume region fields@(first :: rest) motive value branch =
    let tail = "$record.tail." ++ show (length rest)
        self = "$record.self." ++ show (length rest)
        tailType = recordType region rest
        tailRef = NRef region tail
        selfRef = NRef region self
        nextMotive = NLambda region Erased self tailType
          (NApply region motive (NPairValue region (recordType region fields) (fieldRef first) selfRef))
        next = consume region rest nextMotive tailRef (NApply region branch (fieldRef first))
     in NPairCase region motive value
          (NLambda region first.quantity first.token.spelling first.ty (NLambda region Linear tail tailType next))

  -- Substitute needed earlier dependent field names using explicitly erased
  -- applications. Even unused substitutions reduce away, preserving constant
  -- getter result types without requiring a pair eta/conversion rule.
  mentions : String -> Expr -> Bool
  mentions name (NQualifiedRef _ reference) = name == reference
  mentions name (NRecType _ key) = name == key
  mentions name (NRecEnd _ ty) = mentions name ty
  mentions name (NRecMore _ ty tail) = mentions name ty || mentions name tail
  mentions name (NRecFold _ motive base next value) = mentions name motive || mentions name base || mentions name next || mentions name value
  mentions name (NSeqType _ key element) = name == key || mentions name element
  mentions name (NSeqNil _ ty) = mentions name ty
  mentions name (NSeqCons _ ty head tail) = mentions name ty || mentions name head || mentions name tail
  mentions name (NSeqFold _ motive base next value) = mentions name motive || mentions name base || mentions name next || mentions name value
  mentions name (NNominalType _ _ indices shape) = mentionsList name indices || mentions name shape
  mentions name (NNominalValue _ a b) = mentions name a || mentions name b
  mentions name (NNominalCase _ a b c) = mentions name a || mentions name b || mentions name c
  mentions name (NVariantType _ arms) = mentionsArms name arms
  mentions name (NVariantValue _ ty _ payload) = mentions name ty || (case payload of Nothing => False; Just value => mentions name value)
  mentions name (NVariantCase _ a b branches) = mentions name a || mentions name b || mentionsList name branches
  mentions name (NRef _ reference) = name == reference
  mentions name (NImplicitPi _ _ binder domain body) = mentions name domain || (binder /= name && mentions name body)
  mentions name (NConstraintPi _ _ binder domain body) = mentions name domain || (binder /= name && mentions name body)
  mentions name (NPi _ _ binder domain body) = mentions name domain || (binder /= name && mentions name body)
  mentions name (NLambda _ _ binder domain body) = mentions name domain || (binder /= name && mentions name body)
  mentions name (NSigma _ _ _ binder domain body) = mentions name domain || (binder /= name && mentions name body)
  mentions name (NBoxType _ _ ty) = mentions name ty
  mentions name (NBoxValue _ a b) = mentions name a || mentions name b
  mentions name (NBoxCase _ a b c) = mentions name a || mentions name b || mentions name c
  mentions name (NImplementationApply _ _ function) = mentions name function
  mentions name (NDictionaryApply _ _ function argument) = mentions name function || (case argument of Nothing => False; Just value => mentions name value)
  mentions name (NInfix _ f a b) = mentions name f || mentions name a || mentions name b
  mentions name (NOperators _ a rest) = mentions name a || mentionsOperands name rest
  mentions name (NApply _ a b) = mentions name a || mentions name b
  mentions name (NImplicitApply _ a b) = mentions name a || mentions name b
  mentions name (NAscribe _ a b) = mentions name a || mentions name b
  mentions name (NUnitCase _ a b) = mentions name a || mentions name b
  mentions name (NSequence _ a b) = mentions name a || mentions name b
  mentions name (NDoResult _ a b) = mentions name a || mentions name b
  mentions name (NIf _ a b c) = mentions name a || mentions name b || mentions name c
  mentions name (NPairValue _ a b c) = mentions name a || mentions name b || mentions name c
  mentions name (NEquationLambda _ names signature body) = mentions name signature ||
    (if any (\token => token.spelling == name) names then False else mentions name body)
  mentions name (NPatternLambda _ names body) = not (any (\token => token.spelling == name) names) && mentions name body
  mentions name (NDataCase _ value Nothing arms) = mentions name value || mentionsDataArms name arms
  mentions name (NDataCase _ value (Just motive) arms) = mentions name value || mentions name motive || mentionsDataArms name arms
  mentions name (NCaseEither _ asRecord asData) = mentions name asRecord || mentions name asData
  mentions name (NConstructorCase _ _ c a b motive) = mentions name c || mentions name a || mentions name b || (case motive of Nothing => False; Just result => mentions name result)
  mentions name (NInferCase _ _ a b) = mentions name a || mentions name b
  mentions name (NPairCase _ a b c) = mentions name a || mentions name b || mentions name c
  mentions name (NLet _ _ binder a b c) = mentions name a || mentions name b || (binder /= name && mentions name c)
  mentions name (NDoBind _ binder a b c) = mentions name a || mentions name b || (binder /= name && mentions name c)
  mentions _ _ = False

  -- Keep a dependency-closed subsequence, not all preceding fields. Otherwise
  -- even independent getters generate recursively repeated erased extractions.
  dependencies : List RecordField -> List Expr -> (List RecordField, List Expr)
  dependencies [] needed = ([], needed)
  dependencies (field :: rest) needed =
    let (later, types) = dependencies rest needed
     in if any (mentions field.token.spelling) types
           then (field :: later, field.ty :: types) else (later, types)

  fieldResult : SourceSpan -> List RecordField -> RecordField -> (RecordField -> Expr) -> Expr
  fieldResult region earlier selected extract =
    let relevant = fst (dependencies earlier [selected.ty])
     in foldl (NApply region)
          (foldr (\field, body => NLambda region Erased field.token.spelling field.ty body) selected.ty relevant)
          (map extract relevant)

  extractField : Nat -> SourceSpan -> Expr -> List RecordField -> List RecordField -> RecordField -> Expr -> Expr
  extractField Z region typeRef fields earlier selected value = NRef region "$record.extraction.budget"
  extractField (S fuel) region typeRef fields earlier selected value =
    let self = "$record.extract.self." ++ show (length earlier)
        result = fieldResult region earlier selected
          (\previous => extractField fuel region typeRef fields
            (takeWhile (\field => field.token.spelling /= previous.token.spelling) earlier) previous (NRef region self))
        motive = NLambda region Erased self typeRef result
     in case fields of
          [field] => NBoxCase region motive value (fieldLambdas region fields (fieldRef selected))
          [first, second] => NPairCase region motive value (fieldLambdas region fields (fieldRef selected))
          first :: rest =>
            let tail = "$record.extract.tail." ++ show (length rest)
                tailType = recordType region rest
                body = if first.token.spelling == selected.token.spelling then fieldRef first else
                  extractField fuel region tailType rest (drop 1 earlier) selected (NRef region tail)
             in NPairCase region motive value
                  (NLambda region first.quantity first.token.spelling first.ty (NLambda region Linear tail tailType body))
          [] => NRef region "$record.extraction.empty"

  projectionDeclaration : SourceSpan -> Token -> List RecordParameter -> List RecordField ->
                          List RecordField -> RecordField -> RecordProjection -> Declaration
  projectionDeclaration region recordName params fields earlier selected projection =
    let typeRef = applyParameters region (NQualifiedRef recordName.span recordName.spelling) params
        argument = "$projection.record"
        self = "$projection.self"
        resultAt = \value => fieldResult region earlier selected
          (\previous => extractField (length fields) region typeRef fields
            (takeWhile (\field => field.token.spelling /= previous.token.spelling) earlier) previous value)
        motive = NLambda region Erased self typeRef (resultAt (NRef region self))
        ty = NPi region Linear argument typeRef (resultAt (NRef region argument))
        value = NLambda region Linear argument typeRef
          (consume region fields motive (NRef region argument) (fieldLambdas region fields (fieldRef selected)))
     in Declared True (Between projection.keyword.span.start projection.field.span.finish)
          projection.name.span projection.name.span False Unrestricted projection.name.spelling
          (parameterPis region params ty) (parameterLambdas region params value)

  validateProjection : List RecordField -> RecordProjection -> Either ElaborationError RecordField
  validateProjection fields projection = do
    selected <- case find (\field => field.token.spelling == projection.field.spelling) fields of
      Nothing => Left (ElaborationFailure projection.field.span.start "Unknown projected field")
      Just field => Right field
    if not (allows selected.quantity Linear)
       then Left (ElaborationFailure projection.field.span.start "Erased fields cannot be projected as runtime values") else Right ()
    if any (\field => field.token.spelling /= selected.token.spelling && not (allows field.quantity Erased)) fields
       then Left (ElaborationFailure projection.field.span.start "Projection would discard a linear field; consume all fields with a pattern or an explicitly declared eliminator instead")
       else Right ()
    Right selected

  recordEliminator : RecordDeclaration -> Token -> Token -> Declaration
  recordEliminator sourceRecord keyword eliminatorName =
    let region = sourceRecord.span
        name = sourceRecord.name
        params = sourceRecord.params
        fields = sourceRecord.fields
        typeRef = applyParameters region (NQualifiedRef name.span name.spelling) params
        ctorRef = applyParameters region (NQualifiedRef sourceRecord.constructorName.span sourceRecord.constructorName.spelling) params
        p = "$record.motive"
        value = "$record.value"
        next = "$record.branch"
        self = "$record.self"
        pRef = NRef region p
        valueRef = NRef region value
        nextRef = NRef region next
        bind = NPi region
        lam = NLambda region
        app = NApply region
        motiveType = bind Erased self typeRef (NSort region sourceRecord.level)
        branchType = fieldPis region fields (app pRef (applyFields region ctorRef fields))
        elimType = bind Erased p motiveType (bind Linear value typeRef (bind Linear next branchType (app pRef valueRef)))
        elimValue = lam Erased p motiveType (lam Linear value typeRef (lam Linear next branchType (consume region fields pRef valueRef nextRef)))
     in Declared True (Between keyword.span.start eliminatorName.span.finish)
          eliminatorName.span eliminatorName.span False Unrestricted eliminatorName.spelling
          (parameterPis region params elimType) (parameterLambdas region params elimValue)

  recordDeclarations : RecordDeclaration -> List (RecordProjection, RecordField) -> List Declaration
  recordDeclarations sourceRecord projections =
    let region = sourceRecord.span
        name = sourceRecord.name
        params = sourceRecord.params
        fields = sourceRecord.fields
        typeRef = applyParameters region (NQualifiedRef name.span name.spelling) params
     in [ Declared True region name.span name.span False Erased name.spelling
            (parameterPis region params (NSort name.span sourceRecord.level)) (parameterLambdas region params (recordType region fields)),
          Declared True (Between sourceRecord.constructorKeyword.span.start sourceRecord.constructorName.span.finish)
            sourceRecord.constructorName.span sourceRecord.constructorName.span False Unrestricted sourceRecord.constructorName.spelling
            (parameterPis region params (fieldPis region fields typeRef)) (parameterLambdas region params (fieldLambdas region fields (recordValue region fields))) ] ++
        (case sourceRecord.eliminator of
          Nothing => []
          Just (keyword, eliminatorName) => [recordEliminator sourceRecord keyword eliminatorName]) ++
        map (\(projection, selected) => projectionDeclaration region name params fields
          (takeWhile (\field => field.token.spelling /= selected.token.spelling) fields) selected projection) projections

  validateFields : List String -> List RecordParameter -> List RecordField -> Either ElaborationError ()
  validateFields seen params [] = Right ()
  validateFields seen params (field :: rest) = do
    if elem field.token.spelling seen then Left (ElaborationFailure field.token.span.start "Duplicate record field") else Right ()
    if field.token.spelling == "_" then Left (ElaborationFailure field.token.span.start "Record fields need referenceable names") else Right ()
    if any (\p => p.name == field.token.spelling) params
       then Left (ElaborationFailure field.token.span.start "Record fields must not shadow record parameters") else Right ()
    validateFields (field.token.spelling :: seen) params rest

  validateParameters : List String -> List RecordParameter -> Either ElaborationError ()
  validateParameters seen [] = Right ()
  validateParameters seen (parameter :: rest) = do
    if parameter.quantity /= Erased || parameter.name == "_"
       then Left (ElaborationFailure parameter.span.start "Parameters require explicit 0 and a referenceable name")
       else Right ()
    if elem parameter.name seen
       then Left (ElaborationFailure parameter.span.start "Duplicate parameter") else Right ()
    validateParameters (parameter.name :: seen) rest

  -- This conservative preflight bounds named IR before constructing any record
  -- expansion. Core expansion/checking budgets still apply independently.
  public export
  defaultConstructionBudget : Nat
  defaultConstructionBudget = 200000

  capped : Nat -> Nat
  capped = min (S defaultConstructionBudget)

  syntaxNodes : Expr -> Nat
  syntaxNodes (NRecType _ _) = 1
  syntaxNodes (NRecEnd _ ty) = capped (1 + syntaxNodes ty)
  syntaxNodes (NRecMore _ ty tail) = capped (1 + syntaxNodes ty + syntaxNodes tail)
  syntaxNodes (NRecFold _ motive base next value) = capped (1 + syntaxNodes motive + syntaxNodes base + syntaxNodes next + syntaxNodes value)
  syntaxNodes (NSeqType _ _ element) = capped (1 + syntaxNodes element)
  syntaxNodes (NSeqNil _ ty) = capped (1 + syntaxNodes ty)
  syntaxNodes (NSeqCons _ ty head tail) = capped (1 + syntaxNodes ty + syntaxNodes head + syntaxNodes tail)
  syntaxNodes (NSeqFold _ motive base next value) = capped (1 + syntaxNodes motive + syntaxNodes base + syntaxNodes next + syntaxNodes value)
  syntaxNodes (NNominalType _ _ indices shape) = capped (1 + syntaxListNodes indices + syntaxNodes shape)
  syntaxNodes (NNominalValue _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NNominalCase _ a b c) = capped (1 + syntaxNodes a + syntaxNodes b + syntaxNodes c)
  syntaxNodes (NVariantType _ arms) = capped (1 + syntaxArmNodes arms)
  syntaxNodes (NVariantValue _ ty _ payload) = capped (1 + syntaxNodes ty + (case payload of Nothing => 0; Just value => syntaxNodes value))
  syntaxNodes (NVariantCase _ a b branches) = capped (1 + syntaxNodes a + syntaxNodes b + syntaxListNodes branches)
  syntaxNodes (NBoxType _ _ ty) = capped (1 + syntaxNodes ty)
  syntaxNodes (NBoxValue _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NBoxCase _ a b c) = capped (1 + syntaxNodes a + syntaxNodes b + syntaxNodes c)
  syntaxNodes (NImplicitPi _ _ _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NConstraintPi _ _ _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NImplementationApply _ _ function) = capped (1 + syntaxNodes function)
  syntaxNodes (NDictionaryApply _ _ function argument) = capped (1 + syntaxNodes function + (case argument of Nothing => 0; Just value => syntaxNodes value))
  syntaxNodes (NPi _ _ _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NLambda _ _ _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NSigma _ _ _ _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NInfix _ f a b) = capped (1 + syntaxNodes f + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NOperators _ a rest) = capped (1 + syntaxNodes a + syntaxOperands rest)
  syntaxNodes (NApply _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NImplicitApply _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NAscribe _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NUnitCase _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NSequence _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NDoResult _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NIf _ a b c) = capped (1 + syntaxNodes a + syntaxNodes b + syntaxNodes c)
  syntaxNodes (NPairValue _ a b c) = capped (1 + syntaxNodes a + syntaxNodes b + syntaxNodes c)
  syntaxNodes (NEquationLambda _ names signature body) = capped (1 + length names + syntaxNodes signature + syntaxNodes body)
  syntaxNodes (NPatternLambda _ _ body) = capped (1 + syntaxNodes body)
  syntaxNodes (NDataCase _ value Nothing arms) = capped (1 + syntaxNodes value + syntaxDataArms arms)
  syntaxNodes (NDataCase _ value (Just motive) arms) = capped (1 + syntaxNodes value + syntaxNodes motive + syntaxDataArms arms)
  syntaxNodes (NCaseEither _ asRecord _) = capped (1 + syntaxNodes asRecord)
  syntaxNodes (NConstructorCase _ _ c a b motive) = capped (1 + syntaxNodes c + syntaxNodes a + syntaxNodes b + (case motive of Nothing => 0; Just result => syntaxNodes result))
  syntaxNodes (NInferCase _ _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NPairCase _ a b c) = capped (1 + syntaxNodes a + syntaxNodes b + syntaxNodes c)
  syntaxNodes (NLet _ _ _ a b c) = capped (1 + syntaxNodes a + syntaxNodes b + syntaxNodes c)
  syntaxNodes (NDoBind _ _ a b c) = capped (1 + syntaxNodes a + syntaxNodes b + syntaxNodes c)
  syntaxNodes _ = 1

  fieldTypeNodes : List RecordField -> Nat
  fieldTypeNodes fields = foldl (\accum, field => capped (accum + syntaxNodes field.ty)) 0 fields

  recordTypeNodes : List RecordField -> Nat
  recordTypeNodes [] = 1
  recordTypeNodes [field] = capped (1 + syntaxNodes field.ty)
  recordTypeNodes fields = capped (fieldTypeNodes fields + minus (length fields) 1)

  recordValueNodes : List RecordField -> Nat
  recordValueNodes [] = 1
  recordValueNodes [field] = capped (recordTypeNodes [field] + 2)
  recordValueNodes [first, second] = capped (recordTypeNodes [first, second] + 3)
  recordValueNodes fields@(first :: rest) =
    capped (recordTypeNodes fields + recordValueNodes rest + 2)

  consumeNodes : List RecordField -> Nat -> Nat -> Nat
  consumeNodes [] motive branch = branch
  consumeNodes [field] motive branch = capped (motive + branch + 2)
  consumeNodes [first, second] motive branch = capped (motive + branch + 2)
  consumeNodes fields@(first :: rest) motive branch =
    let tailType = recordTypeNodes rest
        nextMotive = capped (motive + tailType + recordTypeNodes fields + 5)
        next = consumeNodes rest nextMotive (capped (branch + 2))
     in capped (motive + syntaxNodes first.ty + tailType + next + 4)

  -- Count fieldResult without generating its recursively repeated extractions.
  resultNodes : List (String, Nat) -> List RecordField -> RecordField -> Nat
  resultNodes costs earlier selected =
    foldl (\accum, field => capped (accum + 2 + syntaxNodes field.ty +
      maybe 0 id (lookup field.token.spelling costs)))
      (syntaxNodes selected.ty) (fst (dependencies earlier [selected.ty]))

  -- Each row contains extraction sizes for a suffix of the telescope. Build the
  -- shorter-tail row first, then the current row in dependency order. This follows
  -- the generator's sharing-free tree size without exponentially generating it.
  extractionRow : Nat -> List RecordField -> List (String, Nat)
  extractionRow typeNodes [] = []
  extractionRow typeNodes fields@(first :: rest) =
    let tailType = recordTypeNodes rest
        below = extractionRow tailType rest
     in row fields below [] fields []
    where
      row : List RecordField -> List (String, Nat) -> List RecordField ->
            List RecordField -> List (String, Nat) -> List (String, Nat)
      row all below earlier [] costs = costs
      row all below earlier (selected :: following) costs =
        let motive = capped (1 + typeNodes + resultNodes costs earlier selected)
            body = if selected.token.spelling == first.token.spelling then 1
                      else maybe 0 id (lookup selected.token.spelling below)
            cost = case all of
              [a] => capped (motive + syntaxNodes a.ty + 4)
              [a, b] => capped (motive + fieldTypeNodes all + 5)
              _ => capped (motive + syntaxNodes first.ty + recordTypeNodes rest + body + 4)
         in row all below (earlier ++ [selected]) following ((selected.token.spelling, cost) :: costs)

  constructionCost : RecordDeclaration -> List (RecordProjection, RecordField) -> Nat
  constructionCost sourceRecord projections =
    let fields = sourceRecord.fields
        width = length fields
        types = fieldTypeNodes fields
        binders = capped (types + width)
        paramNodes = foldl (\accum, param => capped (accum + 1 + syntaxNodes param.domain)) 0 sourceRecord.params
        typeRef = 1 + 2 * length sourceRecord.params
        motiveType = typeRef + 2
        branchType = capped (binders + typeRef + 2 * width + 2)
        domains = capped (3 + motiveType + typeRef + branchType)
        recordCost = capped (1 + recordTypeNodes fields + 2 * paramNodes)
        ctorCost = capped (binders + typeRef + binders + recordValueNodes fields + 2 * paramNodes)
        elimCost = capped (domains + 3 + domains + consumeNodes fields 1 1 + 2 * paramNodes)
        costs = if null projections then [] else extractionRow typeRef fields
        getterCost = \selected =>
          let earlier = takeWhile (\field => field.token.spelling /= selected.token.spelling) fields
              result = resultNodes costs earlier selected
              motive = capped (1 + typeRef + result)
              branch = capped (binders + 1)
           in capped (2 + 2 * typeRef + result + consumeNodes fields motive branch + 2 * paramNodes)
     in foldl (\accum, pair => capped (accum + getterCost (snd pair)))
          (capped (recordCost + ctorCost + (case sourceRecord.eliminator of Nothing => 0; Just _ => elimCost))) projections

  lowerRecord : Nat -> RecordDeclaration -> Either ElaborationError (Nat, List Declaration)
  lowerRecord budget sourceRecord = do
    if length sourceRecord.params > 8
       then Left (ElaborationFailure sourceRecord.span.start "Record parameter admission budget exhausted (8)") else Right ()
    if null sourceRecord.fields
       then Left (ElaborationFailure sourceRecord.span.start "Records require at least one field") else Right ()
    -- Reject oversized base expansion before even walking dependency graphs.
    if constructionCost sourceRecord [] > budget
       then Left (ElaborationFailure sourceRecord.span.start "Generated declaration construction budget exhausted") else Right ()
    validateParameters [] sourceRecord.params
    validateFields [] sourceRecord.params sourceRecord.fields
    projections <- traverse (\projection => do
      selected <- validateProjection sourceRecord.fields projection
      Right (projection, selected)) sourceRecord.projections
    let cost = constructionCost sourceRecord projections
    if cost > budget
       then Left (ElaborationFailure sourceRecord.span.start "Generated declaration construction budget exhausted") else Right ()
    let generated = recordDeclarations sourceRecord projections
    let observed = foldl (\accum, decl => capped (accum + syntaxNodes decl.expected + syntaxNodes decl.value)) 0 generated
    if observed > cost
       then Left (ElaborationFailure sourceRecord.span.start "Internal record construction estimate was insufficient") else Right ()
    Right (cost, map (\decl => { exported := sourceRecord.exported } decl) generated)

  admit : Nat -> List String -> List Declaration -> Either ElaborationError (Nat, List String)
  admit slots seen [] = Right (slots, seen)
  admit Z seen (decl :: _) = Left (ElaborationFailure decl.nameSpan.start "Elaborated declaration budget exhausted")
  admit (S slots) seen (decl :: rest) =
    if elem decl.name seen then Left (ElaborationFailure decl.nameSpan.start ("Duplicate declaration " ++ show decl.name))
       else admit slots (decl.name :: seen) rest

  dictionaryTarget : Expr -> List Expr -> Maybe (String, List Expr)
  dictionaryTarget (NApply _ function argument) args = dictionaryTarget function (argument :: args)
  dictionaryTarget (NRef _ name) args = Just (name, args)
  dictionaryTarget (NQualifiedRef _ name) args = Just (name, args)
  dictionaryTarget _ args = Nothing

  validateMethods : List String -> List String -> List MethodDefinition -> Either ElaborationError ()
  validateMethods allowed seen [] = Right ()
  validateMethods allowed seen (method :: rest) = do
    if elem method.name.spelling seen
       then Left (ElaborationFailure method.name.span.start "Duplicate implementation method") else Right ()
    if not (elem method.name.spelling allowed)
       then Left (ElaborationFailure method.name.span.start ("Unknown implementation method " ++ method.name.spelling)) else Right ()
    validateMethods allowed (method.name.spelling :: seen) rest

  lowerImplementation : List InterfaceSchema -> List String -> List String -> Nat -> ImplementationDefinition -> Either ElaborationError (Nat, List Declaration)
  lowerImplementation schemas imported seen budget block = do
    let (params, result) = implementationTelescope block.target
    (target, args) <- case dictionaryTarget result [] of
      Nothing => Left (ElaborationFailure (extent result).start "Implementation block result must name a visible interface")
      Just result => Right result
    schema <- case find (\schema => schema.name == target) schemas of
      Nothing =>
        let matches = qualifiedMatches target imported in
        if not (elem target seen) && length matches > 1
          then Left (ElaborationFailure (extent result).start
            ("Ambiguous imported interface " ++ target ++ "; candidates: " ++ concat (intersperse ", " matches) ++ "; use a qualified name"))
          else Left (ElaborationFailure (extent result).start
            "Interface schema unavailable for method block; use a visible interface or an explicit dictionary expression")
      Just schema => Right schema
    if not schema.constructorVisible
       then Left (ElaborationFailure (extent result).start "Implementation block requires the interface constructor to be imported") else Right ()
    if length args /= schema.parameterCount
       then Left (ElaborationFailure (extent result).start "Implementation block interface parameters must be explicit") else Right ()
    validateMethods schema.methods [] block.methods
    values <- traverse (\method => case find (\body => body.name.spelling == method) block.methods of
      Nothing => Left (ElaborationFailure block.name.span.start ("Missing implementation method " ++ method))
      Just body => Right body.value) schema.methods
    let arguments = args ++ values
    let cost = foldl (\accum, value => capped (accum + 1 + syntaxNodes value))
                 (foldl (\accum, parameter => capped (accum + 1 + syntaxNodes parameter.domain))
                   (capped (1 + syntaxNodes block.target)) params) arguments
    if cost > budget
       then Left (ElaborationFailure block.name.span.start "Generated declaration construction budget exhausted") else Right ()
    let packed = foldl (NApply block.span) (NQualifiedRef block.name.span schema.constructorName) arguments
    let value = foldr (\parameter, body => NLambda parameter.span parameter.quantity parameter.name parameter.domain body) packed params
    let generated = { dictionary := True } (Declared True block.span block.name.span block.name.span
                      block.exported Unrestricted block.name.spelling block.target value)
    if capped (syntaxNodes generated.expected + syntaxNodes generated.value) > cost
       then Left (ElaborationFailure block.name.span.start "Internal implementation construction estimate was insufficient") else Right ()
    Right (cost, [generated])

  lowerItem : Maybe String -> List InterfaceSchema -> List String -> List String -> Nat -> AuthoredDeclaration -> Either ElaborationError (Nat, List Declaration)
  lowerItem moduleName schemas imported seen nodes (MutualItem group) =
    Left (ElaborationFailure group.span.start "Mutual groups require named-module checking")
  lowerItem moduleName schemas imported seen nodes (MutualDataItem span members) = case moduleName of
    Nothing => Left (ElaborationFailure span.start "Mutual data requires a named module")
    Just qualifier => do
      (used, formers, constructors) <- groupDeclarations qualifier nodes members
      Right (used, formers ++ constructors)
  lowerItem moduleName schemas imported seen nodes (DataItem sourceData) = case moduleName of
    Nothing => Left (ElaborationFailure sourceData.name.span.start "Data declarations require a named module")
    Just qualifier => lowerData qualifier nodes sourceData
  lowerItem moduleName schemas imported seen nodes (Ordinary decl) = Right (0, [decl])
  lowerItem moduleName schemas imported seen nodes (RecordItem sourceRecord) = lowerRecord nodes sourceRecord
  lowerItem moduleName schemas imported seen nodes (InterfaceItem sourceRecord) = do
    if not (null sourceRecord.projections)
       then Left (ElaborationFailure sourceRecord.span.start "Interface methods generate getters; explicit projections are not allowed") else Right ()
    traverse_ (\field => if field.quantity /= Unrestricted
      then Left (ElaborationFailure field.token.span.start "Interface methods require unrestricted fields; method argument quantities remain explicit")
      else Right ()) sourceRecord.fields
    let methods = map (\field => Projected field.token field.token field.token) sourceRecord.fields
    lowerRecord nodes ({ projections := methods } sourceRecord)
  lowerItem moduleName schemas imported seen nodes (ImplementationItem decl) =
    if decl.quantity /= Unrestricted
       then Left (ElaborationFailure decl.nameSpan.start "Implementations require unrestricted named dictionary values")
       else Right (0, [{ dictionary := True } decl])

  lowerItem moduleName schemas imported seen nodes (ImplementationBlock block) = lowerImplementation schemas imported seen nodes block

  authoredPosition : AuthoredDeclaration -> Position
  authoredPosition (MutualDataItem span _) = span.start
  authoredPosition (MutualItem group) = group.span.start
  authoredPosition (DataItem sourceData) = sourceData.name.span.start
  authoredPosition (Ordinary decl) = decl.nameSpan.start
  authoredPosition (ImplementationItem decl) = decl.nameSpan.start
  authoredPosition (ImplementationBlock block) = block.name.span.start
  authoredPosition (RecordItem sourceRecord) = sourceRecord.name.span.start
  authoredPosition (InterfaceItem sourceRecord) = sourceRecord.name.span.start

  -- A general recursive family is registered before the declarations that mention it.
  familyItems : Maybe String -> AuthoredDeclaration -> List LoweredItem
  familyItems (Just qualifier) (DataItem sourceData) =
    case dataKey (forget (Data.String.split (== '.') qualifier)) sourceData.name.spelling of
      Right key => if generalRecursive key sourceData then [DataFamily sourceData key] else []
      Left _ => []
  familyItems (Just qualifier) (MutualDataItem _ members) =
    [DataFamilies (mapMaybe (\member => case dataKey (forget (Data.String.split (== '.') qualifier)) member.name.spelling of
      Right key => Just (member, key)
      Left _ => Nothing) members)]
  familyItems _ _ = []

  lowerModule : Maybe String -> List InterfaceSchema -> List String -> Nat -> Nat -> List String -> List AuthoredDeclaration -> Either ElaborationError (List LoweredItem)
  lowerModule moduleName schemas imported nodes slots seen [] = Right []
  lowerModule moduleName schemas imported nodes slots seen (item :: rest) = do
    if length (bindingSites item) > slots
       then Left (ElaborationFailure (authoredPosition item) "Elaborated declaration budget exhausted") else Right ()
    (used, declarations, lowered) <- case item of
      MutualItem group => case moduleName of
        Nothing => Left (ElaborationFailure group.span.start "Mutual groups require a named module")
        Just _ =>
          if boundedNatBoolGroup group then Right (0, [group.first, group.second], [MutualNatBool group]) else do
            declarations <- generalMutual group
            Right (0, declarations, map Single declarations)
      _ => do
        (used, declarations) <- lowerItem moduleName schemas imported seen nodes item
        Right (used, declarations, familyItems moduleName item ++ map Single declarations)
    (remaining, names) <- admit slots seen declarations
    let retained = filter (\schema => not (elem schema.name (map name (bindingSites item)))) schemas
    let visible = case item of InterfaceItem authored => localSchemas moduleName authored ++ retained; _ => retained
    following <- lowerModule moduleName visible imported (minus nodes used) remaining names rest
    Right (lowered ++ following)

  public export
  elaborateModuleItemsInWithImports : Maybe String -> List InterfaceSchema -> List String -> Nat -> List AuthoredDeclaration -> Either ElaborationError (List LoweredItem)
  elaborateModuleItemsInWithImports moduleName schemas imported slots = lowerModule moduleName schemas imported defaultConstructionBudget slots []

  lower : Maybe String -> List InterfaceSchema -> List String -> Nat -> Nat -> List String -> List AuthoredDeclaration -> Either ElaborationError (List Declaration)
  lower moduleName schemas imported nodes slots seen [] = Right []
  lower moduleName schemas imported nodes slots seen (item :: rest) = do
    if length (bindingSites item) > slots
       then Left (ElaborationFailure (authoredPosition item) "Elaborated declaration budget exhausted") else Right ()
    (used, declarations) <- lowerItem moduleName schemas imported seen nodes item
    (remaining, names) <- admit slots seen declarations
    -- A newly declared local name shadows an imported short schema just as it
    -- shadows an imported value. Qualified imported schemas remain available.
    let retained = filter (\schema => not (elem schema.name (map name (bindingSites item)))) schemas
    let visible = case item of InterfaceItem authored => localSchemas moduleName authored ++ retained; _ => retained
    following <- lower moduleName visible imported (minus nodes used) remaining names rest
    Right (declarations ++ following)

  ||| Imported schemas are supplied only from checked direct dependencies by drivers.
  public export
  elaborateDeclarationsIn : Maybe String -> List InterfaceSchema -> Nat -> List AuthoredDeclaration -> Either ElaborationError (List Declaration)
  elaborateDeclarationsIn moduleName schemas slots = lower moduleName schemas [] defaultConstructionBudget slots []

  ||| Imported names only inform ambiguity diagnostics, never checking authority.
  public export
  elaborateDeclarationsInWithImports : Maybe String -> List InterfaceSchema -> List String -> Nat -> List AuthoredDeclaration -> Either ElaborationError (List Declaration)
  elaborateDeclarationsInWithImports moduleName schemas imported slots = lower moduleName schemas imported defaultConstructionBudget slots []

  ||| Override the construction admission for named-module lowering; resulting
  ||| declarations remain untrusted and require independent core checking.
  public export
  elaborateDeclarationsInWithBudget : Maybe String -> List InterfaceSchema -> Nat -> Nat -> List AuthoredDeclaration -> Either ElaborationError (List Declaration)
  elaborateDeclarationsInWithBudget moduleName schemas nodes slots = lower moduleName schemas [] (min nodes defaultConstructionBudget) slots []

  ||| Ordinary headerless declarations retain their nonrecursive typed-let lowering.
  public export
  lowerDeclarations : Position -> List Declaration -> Expr
  lowerDeclarations end [] = NRef (Between end end) "main"
  lowerDeclarations end (decl :: rest) =
    NLet (Between decl.span.start end) decl.quantity decl.name decl.expected decl.value
         (lowerDeclarations end rest)

  ||| Pure, bounded lowering. This validates declaration policy, not core typing.
  public export
  elaborateDeclarations : Nat -> List AuthoredDeclaration -> Either ElaborationError (List Declaration)
  elaborateDeclarations budget = lower Nothing [] [] defaultConstructionBudget budget []

  ||| Override the generated-IR budget (up to the default safety ceiling).
  ||| Source and expanded-core/checker limits remain independent.
  public export
  elaborateDeclarationsWithBudget : Nat -> Nat -> List AuthoredDeclaration -> Either ElaborationError (List Declaration)
  elaborateDeclarationsWithBudget nodes slots = lower Nothing [] [] (min nodes defaultConstructionBudget) slots []


  mentionsOperands : String -> List (Token, Expr) -> Bool
  mentionsOperands name [] = False
  mentionsOperands name ((op, operand) :: rest) = name == op.spelling || mentions name operand || mentionsOperands name rest

  syntaxOperands : List (Token, Expr) -> Nat
  syntaxOperands [] = 0
  syntaxOperands ((_, operand) :: rest) = capped (1 + syntaxNodes operand + syntaxOperands rest)

  mentionsDataArms : String -> List (Token, List Token, Expr) -> Bool
  mentionsDataArms name [] = False
  mentionsDataArms name ((constructor, binder, body) :: rest) =
    name == constructor.spelling || (not (any (\token => token.spelling == name) binder) && mentions name body) || mentionsDataArms name rest

  syntaxDataArms : List (Token, List Token, Expr) -> Nat
  syntaxDataArms [] = 0
  syntaxDataArms ((_, _, body) :: rest) = capped (1 + syntaxNodes body + syntaxDataArms rest)

  mentionsList : String -> List Expr -> Bool
  mentionsList name [] = False
  mentionsList name (x :: xs) = mentions name x || mentionsList name xs

  mentionsArms : String -> List (Maybe (Quantity, Expr)) -> Bool
  mentionsArms name [] = False
  mentionsArms name (Nothing :: xs) = mentionsArms name xs
  mentionsArms name (Just (_, ty) :: xs) = mentions name ty || mentionsArms name xs

  syntaxListNodes : List Expr -> Nat
  syntaxListNodes [] = 0
  syntaxListNodes (x :: xs) = capped (1 + syntaxNodes x + syntaxListNodes xs)

  syntaxArmNodes : List (Maybe (Quantity, Expr)) -> Nat
  syntaxArmNodes [] = 0
  syntaxArmNodes (Nothing :: xs) = capped (1 + syntaxArmNodes xs)
  syntaxArmNodes (Just (_, ty) :: xs) = capped (1 + syntaxNodes ty + syntaxArmNodes xs)

  dataShape : DataDeclaration -> Expr
  dataShape sourceData = NVariantType sourceData.span (map (\ctor => case ctor.fields of
    [] => Nothing
    [field] => Just (field.quantity, field.ty)
    fields => Just (Linear, recordType ctor.span fields)) sourceData.constructors)

  dataBranchName : Nat -> String
  dataBranchName tag = "$data.branch." ++ show tag

  dataBranches : Nat -> List DataConstructor -> List (Nat, DataConstructor)
  dataBranches tag [] = []
  dataBranches tag (ctor :: rest) = (tag, ctor) :: dataBranches (S tag) rest

  dataConstructorDeclaration : DataDeclaration -> Nat -> DataConstructor -> Declaration
  dataConstructorDeclaration sourceData tag ctor =
    let region = ctor.span
        typeRef = applyParameters region (NQualifiedRef sourceData.name.span sourceData.name.spelling) sourceData.params
        payload = case ctor.fields of
          [] => Nothing
          [field] => Just (fieldRef field)
          fields => Just (recordValue region fields)
        value = NNominalValue region typeRef (NVariantValue region (dataShape sourceData) tag payload)
     in Declared True region ctor.name.span ctor.name.span sourceData.exported Unrestricted ctor.name.spelling
          (constructorParameterPis sourceData.implicitConstructors region sourceData.params (fieldPis region ctor.fields typeRef))
          (parameterLambdas region sourceData.params (fieldLambdas region ctor.fields value))

  dataPayloadBranch : SourceSpan -> Expr -> Expr -> Expr -> (Nat, DataConstructor) -> Expr
  dataPayloadBranch region shape typeRef pRef (tag, ctor) =
    let next = NRef region (dataBranchName tag)
        packType = recordType region ctor.fields
        self = "$data.self"
        packed = "$data.packed"
        packMotive = NLambda region Erased self packType
          (NApply region pRef (NNominalValue region typeRef (NVariantValue region shape tag (Just (NRef region self)))))
     in case ctor.fields of
          [] => next
          [_] => next
          _ => NLambda region Linear packed packType (consume region ctor.fields packMotive (NRef region packed) next)

  dataEliminator : DataDeclaration -> Token -> Token -> Declaration
  dataEliminator sourceData keyword name =
    let region = sourceData.span
        params = sourceData.params
        shape = dataShape sourceData
        typeRef = applyParameters region (NQualifiedRef sourceData.name.span sourceData.name.spelling) params
        p = "$data.motive"
        value = "$data.value"
        self = "$data.self"
        packed = "$data.packed"
        choice = "$data.choice"
        pRef = NRef region p
        app = NApply region
        motiveType = NPi region Erased self typeRef (NSort region sourceData.level)
        entries = dataBranches 0 sourceData.constructors
        branchType = \ctor => fieldPis region ctor.fields
          (app pRef (applyFields region (applyConstructorParameters sourceData.implicitConstructors region (NQualifiedRef ctor.name.span ctor.name.spelling) params) ctor.fields))
        branchField = \entry => Field (Located Name (dataBranchName (fst entry)) region) Unrestricted (branchType (snd entry))
        branches = map branchField entries
        fullMotive = NLambda region Erased self shape (app pRef (NNominalValue region typeRef (NRef region self)))
        body = NNominalCase region pRef (NRef region value)
          (NLambda region Linear choice shape (NVariantCase region fullMotive (NRef region choice) (map (dataPayloadBranch region shape typeRef pRef) entries)))
        ty = NPi region Erased p motiveType (NPi region Linear value typeRef (fieldPis region branches (app pRef (NRef region value))))
        term = NLambda region Erased p motiveType (NLambda region Linear value typeRef (fieldLambdas region branches body))
     in Declared True (Between keyword.span.start name.span.finish) name.span name.span sourceData.exported Unrestricted name.spelling
          (parameterPis region params ty) (parameterLambdas region params term)

  dataCost : DataDeclaration -> Nat
  dataCost sourceData =
    let params = foldl (\accum, param => capped (accum + 1 + syntaxNodes param.domain)) 0 sourceData.params
        reference = 1 + 2 * length sourceData.params
        shape = 1 + foldl (\accum, ctor => capped (accum + 1 + (case ctor.fields of [] => 0; [field] => syntaxNodes field.ty; fields => recordTypeNodes fields))) 0 sourceData.constructors
        nominal = 1 + 2 * length sourceData.params + shape
        family = 2 * params + nominal + 3
        ctorCost = \ctor => let binders = length ctor.fields + fieldTypeNodes ctor.fields
                             in 2 * params + 2 * binders + 2 * reference + shape +
                                (case ctor.fields of [] => 0; [_] => 1; fields => recordValueNodes fields) + 2
        branchType = \ctor => length ctor.fields + fieldTypeNodes ctor.fields + reference + 2 * length ctor.fields + 2
        domains = (reference + 3) + (reference + 1) + foldl (\accum, ctor => capped (accum + 1 + branchType ctor)) 0 sourceData.constructors
        branchValue = \ctor => case ctor.fields of
          [] => 1
          [_] => 1
          fields => let pack = recordTypeNodes fields
                     in 1 + pack + consumeNodes fields (pack + reference + shape + 6) 1
        branchList = foldl (\accum, ctor => capped (accum + 1 + branchValue ctor)) 0 sourceData.constructors
        helper = 2 * params + 2 * domains + 2 * shape + reference + 14 + branchList
     in capped (family + foldl (\accum, ctor => capped (accum + ctorCost ctor)) 0 sourceData.constructors +
          (case sourceData.eliminator of Nothing => 0; Just _ => helper))

  -- Initial recursive source data is a closed two-constructor unary spine.
  -- The only recursive occurrence is the entire linear field domain; the core
  -- RecType intrinsically fixes that strictly positive shape.
  unaryRecursiveShape : String -> DataDeclaration -> Maybe (DataConstructor, DataConstructor, RecordField)
  unaryRecursiveShape key sourceData =
    if not (null sourceData.params) || sourceData.level /= 0 then Nothing else
      case sourceData.constructors of
        [first, second] => case (first.fields, second.fields) of
          ([], [field]) => accept first second field
          ([field], []) => accept second first field
          _ => Nothing
        _ => Nothing
    where
      accept : DataConstructor -> DataConstructor -> RecordField -> Maybe (DataConstructor, DataConstructor, RecordField)
      accept terminal successor field =
        if field.quantity /= Linear || field.token.spelling == sourceData.name.spelling then Nothing else
          case field.ty of
            NRef _ target => if target == sourceData.name.spelling then Just (terminal, successor, field) else Nothing
            NQualifiedRef _ target => if target == key then Just (terminal, successor, field) else Nothing
            _ => Nothing

  recursiveEliminator : DataDeclaration -> DataConstructor -> DataConstructor -> Token -> Token -> Declaration
  recursiveEliminator sourceData terminal successor keyword name =
    let region = sourceData.span
        ty = NQualifiedRef sourceData.name.span sourceData.name.spelling
        p = "$rec.motive"
        self = "$rec.self"
        base = "$rec.base"
        step = "$rec.step"
        tail = "$rec.tail"
        ih = "$rec.ih"
        value = "$rec.value"
        pRef = NRef region p
        app = NApply region
        motiveTy = NPi region Erased self ty (NSort region 0)
        baseTy = app pRef (NQualifiedRef terminal.name.span terminal.name.spelling)
        stepTy = NPi region Erased tail ty
          (NPi region Linear ih (app pRef (NRef region tail))
            (app pRef (app (NQualifiedRef successor.name.span successor.name.spelling) (NRef region tail))))
        resultTy = NPi region Erased p motiveTy (NPi region Linear base baseTy
          (NPi region Unrestricted step stepTy (NPi region Linear value ty (app pRef (NRef region value)))))
        result = NLambda region Erased p motiveTy (NLambda region Linear base baseTy
          (NLambda region Unrestricted step stepTy (NLambda region Linear value ty
            (NRecFold region pRef (NRef region base) (NRef region step) (NRef region value)))))
     in Declared True (Between keyword.span.start name.span.finish) name.span name.span sourceData.exported Unrestricted name.spelling resultTy result

  lowerUnaryRecursiveData : String -> Nat -> DataDeclaration -> DataConstructor -> DataConstructor -> RecordField -> Either ElaborationError (Nat, List Declaration)
  lowerUnaryRecursiveData key budget sourceData terminal successor field = do
    -- A fixed upper reservation precedes constructing these fixed templates;
    -- the actual named-IR node count is checked before returning them.
    let estimate = case sourceData.eliminator of Nothing => 64; Just _ => 512
    if estimate > budget then Left (ElaborationFailure sourceData.name.span.start "Generated recursive data construction budget exhausted") else Right ()
    validateFields [] [] successor.fields
    let region = sourceData.span
    let own = sourceData.name.spelling
    traverse_ (\ctor => case ctor.result of
      NRef _ target => if target == own then Right () else Left (ElaborationFailure (extent ctor.result).start "Recursive constructor result must name its data type")
      NQualifiedRef _ target => if target == key then Right () else Left (ElaborationFailure (extent ctor.result).start "Recursive constructor result must name its data type")
      _ => Left (ElaborationFailure (extent ctor.result).start "Recursive constructor result must name its data type")) sourceData.constructors
    let ty = NQualifiedRef sourceData.name.span own
    let family = Declared True region sourceData.name.span sourceData.name.span sourceData.exported Erased own
                   (NSort sourceData.name.span 0) (NRecType region key)
    let nil = Declared True terminal.span terminal.name.span terminal.name.span sourceData.exported Unrestricted terminal.name.spelling
                ty (NRecEnd terminal.span ty)
    let more = Declared True successor.span successor.name.span successor.name.span sourceData.exported Unrestricted successor.name.spelling
                 (NPi successor.span Linear field.token.spelling ty ty)
                 (NLambda successor.span Linear field.token.spelling ty (NRecMore successor.span ty (fieldRef field)))
    let generated = [family, nil, more] ++
          (case sourceData.eliminator of Nothing => []; Just (keyword, name) => [recursiveEliminator sourceData terminal successor keyword name])
    let actual = foldl (\accum, decl => capped (accum + syntaxNodes decl.expected + syntaxNodes decl.value)) 0 generated
    if actual > estimate then Left (ElaborationFailure sourceData.name.span.start "Internal recursive data construction estimate was insufficient") else Right ()
    Right (estimate, generated)

  -- Exactly one erased Type0 parameter, a terminal, and a linear element plus
  -- a linear direct self tail. No other parameter, index or payload shape is
  -- inferred from metadata; unsupported recursive declarations fail closed.
  sequenceRecursiveShape : String -> DataDeclaration -> Maybe (RecordParameter, DataConstructor, DataConstructor, RecordField, RecordField)
  sequenceRecursiveShape key sourceData = case sourceData.params of
    [parameter] => case parameter.domain of
      NSort _ 0 => if parameter.quantity /= Erased || parameter.name == sourceData.name.spelling || sourceData.level /= 0
        then Nothing else case sourceData.constructors of
          [first, second] => case (first.fields, second.fields) of
            ([], [head, tail]) => accept parameter first second head tail
            ([head, tail], []) => accept parameter second first head tail
            _ => Nothing
          _ => Nothing
      _ => Nothing
    _ => Nothing
    where
      accept : RecordParameter -> DataConstructor -> DataConstructor -> RecordField -> RecordField -> Maybe (RecordParameter, DataConstructor, DataConstructor, RecordField, RecordField)
      accept parameter terminal successor head tail =
        if head.quantity /= Linear || tail.quantity /= Linear ||
           head.token.spelling == sourceData.name.spelling || tail.token.spelling == sourceData.name.spelling
          then Nothing else case (head.ty, tail.ty) of
            (NRef _ element, NApply _ (NRef _ target) (NRef _ index)) =>
              if element == parameter.name && target == sourceData.name.spelling && index == parameter.name
                then Just (parameter, terminal, successor, head, tail) else Nothing
            (NRef _ element, NApply _ (NQualifiedRef _ target) (NRef _ index)) =>
              if element == parameter.name && target == key && index == parameter.name
                then Just (parameter, terminal, successor, head, tail) else Nothing
            _ => Nothing

  sequenceEliminator : DataDeclaration -> RecordParameter -> DataConstructor -> DataConstructor -> Token -> Token -> Declaration
  sequenceEliminator sourceData parameter terminal successor keyword name =
    let region = sourceData.span
        params = sourceData.params
        ty = applyParameters region (NQualifiedRef sourceData.name.span sourceData.name.spelling) params
        element = NRef parameter.span parameter.name
        p = "$seq.motive"
        self = "$seq.self"
        base = "$seq.base"
        step = "$seq.step"
        head = "$seq.head"
        tail = "$seq.tail"
        ih = "$seq.ih"
        value = "$seq.value"
        pRef = NRef region p
        app = NApply region
        nilRef = applyConstructorParameters sourceData.implicitConstructors region (NQualifiedRef terminal.name.span terminal.name.spelling) params
        consRef = applyConstructorParameters sourceData.implicitConstructors region (NQualifiedRef successor.name.span successor.name.spelling) params
        motiveTy = NPi region Erased self ty (NSort region 0)
        baseTy = app pRef nilRef
        stepTy = NPi region Linear head element (NPi region Erased tail ty
          (NPi region Linear ih (app pRef (NRef region tail))
            (app pRef (app (app consRef (NRef region head)) (NRef region tail)))))
        resultTy = NPi region Erased p motiveTy (NPi region Linear base baseTy
          (NPi region Unrestricted step stepTy (NPi region Linear value ty (app pRef (NRef region value)))))
        result = NLambda region Erased p motiveTy (NLambda region Linear base baseTy
          (NLambda region Unrestricted step stepTy (NLambda region Linear value ty
            (NSeqFold region pRef (NRef region base) (NRef region step) (NRef region value)))))
     in Declared True (Between keyword.span.start name.span.finish) name.span name.span sourceData.exported Unrestricted name.spelling
          (parameterPis region params resultTy) (parameterLambdas region params result)

  lowerSequenceRecursiveData : String -> Nat -> DataDeclaration -> RecordParameter -> DataConstructor -> DataConstructor -> RecordField -> RecordField -> Either ElaborationError (Nat, List Declaration)
  lowerSequenceRecursiveData key budget sourceData parameter terminal successor head tail = do
    let estimate = case sourceData.eliminator of Nothing => 128; Just _ => 768
    if estimate > budget then Left (ElaborationFailure sourceData.name.span.start "Generated sequence data construction budget exhausted") else Right ()
    validateFields [] sourceData.params successor.fields
    let region = sourceData.span
    let own = sourceData.name.spelling
    traverse_ (\ctor => case dictionaryTarget ctor.result [] of
      Just (target, [NRef _ index]) => if (target == own || target == key) && index == parameter.name
        then Right () else Left (ElaborationFailure (extent ctor.result).start "Sequence constructor result must apply its data type to the parameter")
      _ => Left (ElaborationFailure (extent ctor.result).start "Sequence constructor result must apply its data type to the parameter")) sourceData.constructors
    let params = sourceData.params
    let ty = applyParameters region (NQualifiedRef sourceData.name.span own) params
    let family = Declared True region sourceData.name.span sourceData.name.span sourceData.exported Erased own
          (parameterPis region params (NSort sourceData.name.span 0))
          (parameterLambdas region params (NSeqType region key (NRef parameter.span parameter.name)))
    let nil = Declared True terminal.span terminal.name.span terminal.name.span sourceData.exported Unrestricted terminal.name.spelling
          (constructorParameterPis sourceData.implicitConstructors region params ty)
          (parameterLambdas region params (NSeqNil terminal.span ty))
    let more = Declared True successor.span successor.name.span successor.name.span sourceData.exported Unrestricted successor.name.spelling
          (constructorParameterPis sourceData.implicitConstructors region params (fieldPis region successor.fields ty))
          (parameterLambdas region params (fieldLambdas region successor.fields (NSeqCons successor.span ty (fieldRef head) (fieldRef tail))))
    let generated = [family, nil, more] ++
          (case sourceData.eliminator of Nothing => []; Just (keyword, name) => [sequenceEliminator sourceData parameter terminal successor keyword name])
    let actual = foldl (\accum, decl => capped (accum + syntaxNodes decl.expected + syntaxNodes decl.value)) 0 generated
    if actual > estimate then Left (ElaborationFailure sourceData.name.span.start "Internal sequence data construction estimate was insufficient") else Right ()
    Right (estimate, generated)

  lowerData : String -> Nat -> DataDeclaration -> Either ElaborationError (Nat, List Declaration)
  lowerData qualifier budget sourceData = do
    let estimate = dataCost sourceData
    if estimate > budget then Left (ElaborationFailure sourceData.name.span.start "Generated data construction budget exhausted") else Right ()
    validateParameters [] sourceData.params
    key <- case dataKey (forget (Data.String.split (== '.') qualifier)) sourceData.name.spelling of
      Left error => Left (ElaborationFailure sourceData.name.span.start error.message)
      Right key => Right key
    case (if null sourceData.indices then unaryRecursiveShape key sourceData else Nothing) of
      Just (terminal, successor, field) => lowerUnaryRecursiveData key budget sourceData terminal successor field
      Nothing => case (if null sourceData.indices then sequenceRecursiveShape key sourceData else Nothing) of
        Just (parameter, terminal, successor, head, tail) => lowerSequenceRecursiveData key budget sourceData parameter terminal successor head tail
        Nothing =>
          if generalRecursive key sourceData then lowerGeneralData key budget sourceData
          else lowerNonrecursiveData key estimate sourceData
    where
      lowerNonrecursiveData : String -> Nat -> DataDeclaration -> Either ElaborationError (Nat, List Declaration)
      lowerNonrecursiveData key estimate sourceData = do
        lowerOrdinaryData key estimate sourceData

  -- A recursive declaration that is neither fixed shape: trees, multi-field or multi-constructor
  -- recursion. It is checked as general recursive data, not generated from templates.
  public export
  generalRecursive : String -> DataDeclaration -> Bool
  generalRecursive key sourceData =
    not (null sourceData.indices) ||
    (isNothing (unaryRecursiveShape key sourceData) && isNothing (sequenceRecursiveShape key sourceData) &&
    any (\ctor => any (\field => mentions sourceData.name.spelling field.ty || mentions key field.ty) ctor.fields) sourceData.constructors)

  -- The family and each constructor become ordinary global declarations whose values are the
  -- core constants. The family itself is registered separately (see `DataFamily`), because its
  -- constructor types must be checked with the family already in scope.
  lowerGeneralData : String -> Nat -> DataDeclaration -> Either ElaborationError (Nat, List Declaration)
  lowerGeneralData key budget sourceData = do
    validateParameters [] (sourceData.params ++ sourceData.indices)
    if sourceData.level /= 0 then Left (ElaborationFailure sourceData.name.span.start "General data families must live in Type 0") else Right ()
    if not (null sourceData.indices) && isJust sourceData.eliminator
      then Left (ElaborationFailure sourceData.name.span.start "Indexed families use explicit case motives; generated eliminator helpers are not supported") else Right ()
    let refs = map (\param => NRef param.span param.name) sourceData.params
    let ownName = sourceData.name.spelling
    if any (\param => param.name == ownName || mentions ownName param.domain || mentions key param.domain) sourceData.params
       then Left (ElaborationFailure sourceData.name.span.start "Data parameters must not shadow or reference their own type") else Right ()
    traverse_ (\ctor => do
      validateFields [] sourceData.params ctor.fields
      if any (\field => field.token.spelling == ownName) ctor.fields
         then Left (ElaborationFailure ctor.name.span.start "A field may not be named like its data type") else Right ()
      case dictionaryTarget ctor.result [] of
        Just (target, args) => if (target == ownName || target == key) &&
          mapMaybe (\arg => case arg of NRef _ name => Just name; _ => Nothing) (take (length sourceData.params) args) == map (\p => p.name) sourceData.params &&
          length args == length sourceData.params + length sourceData.indices
          then Right () else Left (ElaborationFailure (extent ctor.result).start "Constructor result must be its data type applied to all parameters in order")
        _ => Left (ElaborationFailure (extent ctor.result).start "Constructor result must name its data type")) sourceData.constructors
    let leading = length sourceData.params
    let allBinders = sourceData.params ++ sourceData.indices
    let allRefs = map (\param => NRef param.span param.name) allBinders
    let applied = foldl (\function, argument => NApply sourceData.span function argument) (NDataType sourceData.span key) allRefs
    let family = Declared True sourceData.span sourceData.name.span sourceData.name.span sourceData.exported Erased ownName
          (parameterPis sourceData.span allBinders (NSort sourceData.name.span sourceData.level))
          (parameterLambdas sourceData.span allBinders applied)
    let constructor = \entry =>
          let ctor = snd entry
              region = ctor.span
              typeRef = ctor.result
           in Declared True region ctor.name.span ctor.name.span sourceData.exported Unrestricted ctor.name.spelling
                (constructorParameterPis sourceData.implicitConstructors region sourceData.params (fieldPis region ctor.fields typeRef))
                (NDataCon region key (fst entry) leading)
    let generated = family :: map constructor (dataBranches 0 sourceData.constructors)
    let actual = foldl (\accum, decl => capped (accum + syntaxNodes decl.expected + syntaxNodes decl.value)) 0 generated
    if actual > budget then Left (ElaborationFailure sourceData.name.span.start "Generated data construction budget exhausted") else Right ()
    Right (actual, generated)

  groupDeclarations : String -> Nat -> List DataDeclaration -> Either ElaborationError (Nat, List Declaration, List Declaration)
  groupDeclarations qualifier budget [] = Right (0, [], [])
  groupDeclarations qualifier budget (member :: rest) = do
    if not (null member.indices) then Left (ElaborationFailure member.name.span.start "Indexed mutual data is not supported") else Right ()
    if isJust member.eliminator then Left (ElaborationFailure member.name.span.start "Mutual data does not generate eliminator helpers") else Right ()
    key <- case dataKey (forget (Data.String.split (== '.') qualifier)) member.name.spelling of
      Left why => Left (ElaborationFailure member.name.span.start why.message)
      Right key => Right key
    (used, generated) <- lowerGeneralData key budget member
    case generated of
      [] => Left (ElaborationFailure member.name.span.start "Internal mutual family lowering failed")
      former :: constructors => do
        (later, formers, remaining) <- groupDeclarations qualifier (minus budget used) rest
        Right (used + later, former :: formers, constructors ++ remaining)

  lowerOrdinaryData : String -> Nat -> DataDeclaration -> Either ElaborationError (Nat, List Declaration)
  lowerOrdinaryData key estimate sourceData = do
    let refs = map (\param => NRef param.span param.name) sourceData.params
    let ownName = sourceData.name.spelling
    if any (\param => param.name == ownName || mentions ownName param.domain || mentions key param.domain) sourceData.params
       then Left (ElaborationFailure sourceData.name.span.start "Data parameters must not shadow or reference their own type") else Right ()
    traverse_ (\ctor => do
      validateFields [] sourceData.params ctor.fields
      if any (\field => field.token.spelling == ownName || mentions ownName field.ty || mentions key field.ty) ctor.fields
         then Left (ElaborationFailure ctor.name.span.start "Recursive data or type-name shadowing is not supported") else Right ()
      case dictionaryTarget ctor.result [] of
        Just (target, args) => if (target == ownName || target == key) &&
          mapMaybe (\arg => case arg of NRef _ name => Just name; _ => Nothing) args == map (\p => p.name) sourceData.params &&
          length args == length sourceData.params
          then Right () else Left (ElaborationFailure (extent ctor.result).start "Constructor result must be its data type applied to all parameters in order")
        _ => Left (ElaborationFailure (extent ctor.result).start "Constructor result must name its data type")) sourceData.constructors
    let family = Declared True sourceData.span sourceData.name.span sourceData.name.span sourceData.exported Erased ownName
          (parameterPis sourceData.span sourceData.params (NSort sourceData.name.span sourceData.level))
          (parameterLambdas sourceData.span sourceData.params
            (NAscribe sourceData.span (NNominalType sourceData.span key refs (dataShape sourceData)) (NSort sourceData.span sourceData.level)))
    let generated = family :: map (\(tag, ctor) => dataConstructorDeclaration sourceData tag ctor) (dataBranches 0 sourceData.constructors) ++
          (case sourceData.eliminator of Nothing => []; Just (keyword, name) => [dataEliminator sourceData keyword name])
    let actual = foldl (\accum, decl => capped (accum + syntaxNodes decl.expected + syntaxNodes decl.value)) 0 generated
    if actual > estimate then Left (ElaborationFailure sourceData.name.span.start "Internal data construction estimate was insufficient") else Right ()
    Right (estimate, generated)
