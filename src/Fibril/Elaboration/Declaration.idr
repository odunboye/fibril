-- Explicit record lowering and admission; generated IR still needs core checking.
module Fibril.Elaboration.Declaration

import Data.List
import Data.String
import Data.List1
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
  mentions name (NQualifiedRef _ reference) = name == reference
  mentions name (NNominalType _ _ indices shape) = mentionsList name indices || mentions name shape
  mentions name (NNominalValue _ a b) = mentions name a || mentions name b
  mentions name (NNominalCase _ a b c) = mentions name a || mentions name b || mentions name c
  mentions name (NVariantType _ arms) = mentionsArms name arms
  mentions name (NVariantValue _ ty _ payload) = mentions name ty || (case payload of Nothing => False; Just value => mentions name value)
  mentions name (NVariantCase _ a b branches) = mentions name a || mentions name b || mentionsList name branches
  mentions name (NRef _ reference) = name == reference
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
  mentions name (NApply _ a b) = mentions name a || mentions name b
  mentions name (NAscribe _ a b) = mentions name a || mentions name b
  mentions name (NUnitCase _ a b) = mentions name a || mentions name b
  mentions name (NSequence _ a b) = mentions name a || mentions name b
  mentions name (NDoResult _ a b) = mentions name a || mentions name b
  mentions name (NIf _ a b c) = mentions name a || mentions name b || mentions name c
  mentions name (NPairValue _ a b c) = mentions name a || mentions name b || mentions name c
  mentions name (NPatternLambda _ names body) = not (any (\token => token.spelling == name) names) && mentions name body
  mentions name (NDataCase _ value motive arms) = mentions name value || mentions name motive || mentionsDataArms name arms
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
  syntaxNodes (NNominalType _ _ indices shape) = capped (1 + syntaxListNodes indices + syntaxNodes shape)
  syntaxNodes (NNominalValue _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NNominalCase _ a b c) = capped (1 + syntaxNodes a + syntaxNodes b + syntaxNodes c)
  syntaxNodes (NVariantType _ arms) = capped (1 + syntaxArmNodes arms)
  syntaxNodes (NVariantValue _ ty _ payload) = capped (1 + syntaxNodes ty + (case payload of Nothing => 0; Just value => syntaxNodes value))
  syntaxNodes (NVariantCase _ a b branches) = capped (1 + syntaxNodes a + syntaxNodes b + syntaxListNodes branches)
  syntaxNodes (NBoxType _ _ ty) = capped (1 + syntaxNodes ty)
  syntaxNodes (NBoxValue _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NBoxCase _ a b c) = capped (1 + syntaxNodes a + syntaxNodes b + syntaxNodes c)
  syntaxNodes (NConstraintPi _ _ _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NImplementationApply _ _ function) = capped (1 + syntaxNodes function)
  syntaxNodes (NDictionaryApply _ _ function argument) = capped (1 + syntaxNodes function + (case argument of Nothing => 0; Just value => syntaxNodes value))
  syntaxNodes (NPi _ _ _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NLambda _ _ _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NSigma _ _ _ _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NInfix _ f a b) = capped (1 + syntaxNodes f + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NApply _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NAscribe _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NUnitCase _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NSequence _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NDoResult _ a b) = capped (1 + syntaxNodes a + syntaxNodes b)
  syntaxNodes (NIf _ a b c) = capped (1 + syntaxNodes a + syntaxNodes b + syntaxNodes c)
  syntaxNodes (NPairValue _ a b c) = capped (1 + syntaxNodes a + syntaxNodes b + syntaxNodes c)
  syntaxNodes (NPatternLambda _ _ body) = capped (1 + syntaxNodes body)
  syntaxNodes (NDataCase _ value motive arms) = capped (1 + syntaxNodes value + syntaxNodes motive + syntaxDataArms arms)
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

  lowerImplementation : List InterfaceSchema -> Nat -> ImplementationDefinition -> Either ElaborationError (Nat, List Declaration)
  lowerImplementation schemas budget block = do
    let (params, result) = implementationTelescope block.target
    (target, args) <- case dictionaryTarget result [] of
      Nothing => Left (ElaborationFailure (extent result).start "Implementation block result must name a visible interface")
      Just result => Right result
    schema <- case find (\schema => schema.name == target) schemas of
      Nothing => Left (ElaborationFailure (extent result).start
        "Interface schema unavailable for method block; use a visible interface or an explicit dictionary expression")
      Just schema => Right schema
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

  lowerItem : Maybe String -> List InterfaceSchema -> Nat -> AuthoredDeclaration -> Either ElaborationError (Nat, List Declaration)
  lowerItem moduleName schemas nodes (DataItem sourceData) = case moduleName of
    Nothing => Left (ElaborationFailure sourceData.name.span.start "Data declarations require a named module")
    Just qualifier => lowerData qualifier nodes sourceData
  lowerItem moduleName schemas nodes (Ordinary decl) = Right (0, [decl])
  lowerItem moduleName schemas nodes (RecordItem sourceRecord) = lowerRecord nodes sourceRecord
  lowerItem moduleName schemas nodes (InterfaceItem sourceRecord) = do
    if not (null sourceRecord.projections)
       then Left (ElaborationFailure sourceRecord.span.start "Interface methods generate getters; explicit projections are not allowed") else Right ()
    traverse_ (\field => if field.quantity /= Unrestricted
      then Left (ElaborationFailure field.token.span.start "Interface methods require unrestricted fields; method argument quantities remain explicit")
      else Right ()) sourceRecord.fields
    let methods = map (\field => Projected field.token field.token field.token) sourceRecord.fields
    lowerRecord nodes ({ projections := methods } sourceRecord)
  lowerItem moduleName schemas nodes (ImplementationItem decl) =
    if decl.quantity /= Unrestricted
       then Left (ElaborationFailure decl.nameSpan.start "Implementations require unrestricted named dictionary values")
       else Right (0, [{ dictionary := True } decl])

  lowerItem moduleName schemas nodes (ImplementationBlock block) = lowerImplementation schemas nodes block

  authoredPosition : AuthoredDeclaration -> Position
  authoredPosition (DataItem sourceData) = sourceData.name.span.start
  authoredPosition (Ordinary decl) = decl.nameSpan.start
  authoredPosition (ImplementationItem decl) = decl.nameSpan.start
  authoredPosition (ImplementationBlock block) = block.name.span.start
  authoredPosition (RecordItem sourceRecord) = sourceRecord.name.span.start
  authoredPosition (InterfaceItem sourceRecord) = sourceRecord.name.span.start

  lower : Maybe String -> List InterfaceSchema -> Nat -> Nat -> List String -> List AuthoredDeclaration -> Either ElaborationError (List Declaration)
  lower moduleName schemas nodes slots seen [] = Right []
  lower moduleName schemas nodes slots seen (item :: rest) = do
    if length (bindingSites item) > slots
       then Left (ElaborationFailure (authoredPosition item) "Elaborated declaration budget exhausted") else Right ()
    (used, declarations) <- lowerItem moduleName schemas nodes item
    (remaining, names) <- admit slots seen declarations
    let visible = case item of InterfaceItem authored => localSchemas moduleName authored ++ schemas; _ => schemas
    following <- lower moduleName visible (minus nodes used) remaining names rest
    Right (declarations ++ following)

  ||| Imported schemas are supplied only from checked direct dependencies by drivers.
  public export
  elaborateDeclarationsIn : Maybe String -> List InterfaceSchema -> Nat -> List AuthoredDeclaration -> Either ElaborationError (List Declaration)
  elaborateDeclarationsIn moduleName schemas slots = lower moduleName schemas defaultConstructionBudget slots []

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
  elaborateDeclarations budget = lower Nothing [] defaultConstructionBudget budget []

  ||| Override the generated-IR budget (up to the default safety ceiling).
  ||| Source and expanded-core/checker limits remain independent.
  public export
  elaborateDeclarationsWithBudget : Nat -> Nat -> List AuthoredDeclaration -> Either ElaborationError (List Declaration)
  elaborateDeclarationsWithBudget nodes slots = lower Nothing [] (min nodes defaultConstructionBudget) slots []


  mentionsDataArms : String -> List (Token, Maybe Token, Expr) -> Bool
  mentionsDataArms name [] = False
  mentionsDataArms name ((constructor, binder, body) :: rest) =
    name == constructor.spelling || (case binder of Just token => if token.spelling == name then False else mentions name body; Nothing => mentions name body) || mentionsDataArms name rest

  syntaxDataArms : List (Token, Maybe Token, Expr) -> Nat
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
          (parameterPis region sourceData.params (fieldPis region ctor.fields typeRef))
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
          (app pRef (applyFields region (applyParameters region (NQualifiedRef ctor.name.span ctor.name.spelling) params) ctor.fields))
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

  lowerData : String -> Nat -> DataDeclaration -> Either ElaborationError (Nat, List Declaration)
  lowerData qualifier budget sourceData = do
    let estimate = dataCost sourceData
    if estimate > budget then Left (ElaborationFailure sourceData.name.span.start "Generated data construction budget exhausted") else Right ()
    validateParameters [] sourceData.params
    key <- case dataKey (forget (Data.String.split (== '.') qualifier)) sourceData.name.spelling of
      Left error => Left (ElaborationFailure sourceData.name.span.start error.message)
      Right key => Right key
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
