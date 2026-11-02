-- Explicit record lowering and admission; generated IR still needs core checking.
module Fibril.Elaboration.Declaration

import Data.List
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Declaration.Syntax

%default total

public export
record ElaborationError where
  constructor ElaborationFailure
  position : Position
  message : String

public export
Show ElaborationError where
  show err = show err.position ++ ": " ++ err.message

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

parameterLambdas : SourceSpan -> List RecordParameter -> Expr -> Expr
parameterLambdas region [] body = body
parameterLambdas region (parameter :: rest) body =
  NLambda region Erased parameter.name parameter.domain (parameterLambdas region rest body)

applyParameters : SourceSpan -> Expr -> List RecordParameter -> Expr
applyParameters region function [] = function
applyParameters region function (parameter :: rest) =
  applyParameters region (NApply region function (NRef parameter.span parameter.name)) rest

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
mentions name (NRef _ reference) = name == reference
mentions name (NPi _ _ binder domain body) = mentions name domain || (binder /= name && mentions name body)
mentions name (NLambda _ _ binder domain body) = mentions name domain || (binder /= name && mentions name body)
mentions name (NSigma _ _ _ binder domain body) = mentions name domain || (binder /= name && mentions name body)
mentions name (NBoxType _ _ ty) = mentions name ty
mentions name (NBoxValue _ a b) = mentions name a || mentions name b
mentions name (NBoxCase _ a b c) = mentions name a || mentions name b || mentions name c
mentions name (NApply _ a b) = mentions name a || mentions name b
mentions name (NAscribe _ a b) = mentions name a || mentions name b
mentions name (NUnitCase _ a b) = mentions name a || mentions name b
mentions name (NSequence _ a b) = mentions name a || mentions name b
mentions name (NDoResult _ a b) = mentions name a || mentions name b
mentions name (NIf _ a b c) = mentions name a || mentions name b || mentions name c
mentions name (NPairValue _ a b c) = mentions name a || mentions name b || mentions name c
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
     then Left (ElaborationFailure projection.field.span.start "Projection would discard a linear field; consume all fields with the eliminator instead")
     else Right ()
  Right selected

recordDeclarations : RecordDeclaration -> List (RecordProjection, RecordField) -> List Declaration
recordDeclarations sourceRecord projections =
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
   in [ Declared True region name.span name.span False Erased name.spelling
          (parameterPis region params (NSort name.span sourceRecord.level)) (parameterLambdas region params (recordType region fields)),
        Declared True (Between sourceRecord.constructorKeyword.span.start sourceRecord.constructorName.span.finish)
          sourceRecord.constructorName.span sourceRecord.constructorName.span False Unrestricted sourceRecord.constructorName.spelling
          (parameterPis region params (fieldPis region fields typeRef)) (parameterLambdas region params (fieldLambdas region fields (recordValue region fields))),
        Declared True (Between sourceRecord.eliminatorKeyword.span.start sourceRecord.eliminatorName.span.finish)
          sourceRecord.eliminatorName.span sourceRecord.eliminatorName.span False Unrestricted sourceRecord.eliminatorName.spelling
          (parameterPis region params elimType) (parameterLambdas region params elimValue) ] ++
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
     then Left (ElaborationFailure parameter.span.start "Record parameters require explicit 0 and a referenceable name")
     else Right ()
  if elem parameter.name seen
     then Left (ElaborationFailure parameter.span.start "Duplicate record parameter") else Right ()
  validateParameters (parameter.name :: seen) rest

-- This conservative preflight bounds named IR before constructing any record
-- expansion. Core expansion/checking budgets still apply independently.
public export
defaultConstructionBudget : Nat
defaultConstructionBudget = 200000

capped : Nat -> Nat
capped = min (S defaultConstructionBudget)

syntaxNodes : Expr -> Nat
syntaxNodes (NBoxType _ _ ty) = capped (1 + syntaxNodes ty)
syntaxNodes (NBoxValue _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
syntaxNodes (NBoxCase _ a b c) = capped (1 + syntaxNodes a + syntaxNodes b + syntaxNodes c)
syntaxNodes (NPi _ _ _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
syntaxNodes (NLambda _ _ _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
syntaxNodes (NSigma _ _ _ _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
syntaxNodes (NApply _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
syntaxNodes (NAscribe _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
syntaxNodes (NUnitCase _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
syntaxNodes (NSequence _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
syntaxNodes (NDoResult _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
syntaxNodes (NIf _ a b c) = capped (1 + syntaxNodes a + syntaxNodes b + syntaxNodes c)
syntaxNodes (NPairValue _ a b c) = capped (1 + syntaxNodes a + syntaxNodes b + syntaxNodes c)
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
        (capped (recordCost + ctorCost + elimCost)) projections

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

lowerItem : Nat -> AuthoredDeclaration -> Either ElaborationError (Nat, List Declaration)
lowerItem nodes (Ordinary decl) = Right (0, [decl])
lowerItem nodes (RecordItem sourceRecord) = lowerRecord nodes sourceRecord

lower : Nat -> Nat -> List String -> List AuthoredDeclaration -> Either ElaborationError (List Declaration)
lower nodes slots seen [] = Right []
lower nodes slots seen (item :: rest) = do
  if length (bindingSites item) > slots
     then Left (ElaborationFailure (case item of Ordinary decl => decl.nameSpan.start; RecordItem sourceRecord => sourceRecord.name.span.start) "Elaborated declaration budget exhausted") else Right ()
  (used, declarations) <- lowerItem nodes item
  (remaining, names) <- admit slots seen declarations
  following <- lower (minus nodes used) remaining names rest
  Right (declarations ++ following)

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
elaborateDeclarations budget = lower defaultConstructionBudget budget []

||| Override the generated-IR budget (up to the default safety ceiling).
||| Source and expanded-core/checker limits remain independent.
public export
elaborateDeclarationsWithBudget : Nat -> Nat -> List AuthoredDeclaration -> Either ElaborationError (List Declaration)
elaborateDeclarationsWithBudget nodes slots = lower (min nodes defaultConstructionBudget) slots []
