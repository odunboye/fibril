-- Shared lexical traversal. Project clients supply checked qualified bindings.
module Fibril.Source.Navigation

import Data.List
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Parser
import Fibril.Source.Declaration
import Fibril.Source.Symbol

%default total

public export
record ReferenceTo (destination : Type) where
  constructor RefersTo
  origin : SourceSpan
  target : destination

public export
Reference : Type
Reference = ReferenceTo SourceSpan

record Walker (destination : Type) where
  constructor Walking
  tokens : List Token
  localTarget : SourceSpan -> destination
  qualifiedTarget : String -> Maybe destination
  globalTarget : String -> Maybe destination
  moduleTarget : String -> Maybe destination

Environment : Type -> Type
Environment destination = List (String, Maybe destination)

lexicalTarget : String -> Environment destination -> Maybe destination
lexicalTarget name [] = Nothing
lexicalTarget name ((bound, target) :: rest) =
  if name == "_" then Nothing
  else if name == bound then target else lexicalTarget name rest

-- Grouped expression spans may include parentheses. Select the actual name token.
nameToken : String -> SourceSpan -> List Token -> Maybe SourceSpan
nameToken name region tokens = map span $ find
  (\token => token.kind == Name && token.spelling == name &&
             token.span.start.offset >= region.start.offset &&
             token.span.finish.offset <= region.finish.offset) tokens

-- Select the last name before the domain, excluding the domain itself. A do
-- statement span can also contain its block's earlier result annotation.
binderToken : String -> SourceSpan -> Expr -> List Token -> Maybe SourceSpan
binderToken name region domain tokens =
  if name == "_" then Nothing else
    nameToken name (Between region.start (extent domain).start) (reverse tokens)

self : Walker destination -> Maybe SourceSpan -> List (ReferenceTo destination)
self context Nothing = []
self context (Just span) = [RefersTo span (context.localTarget span)]

-- Qualified AST nodes, not text matches, authorize module-qualifier links.
-- The callback receives the full qualified name and resolves its module prefix.
qualifierReferences : Walker destination -> SourceSpan -> SourceSpan -> String -> List (ReferenceTo destination)
qualifierReferences context region final name = case context.moduleTarget name of
  Nothing => []
  Just target => case filter (\token => token.kind == Name &&
      token.span.start.offset >= region.start.offset &&
      token.span.finish.offset <= final.start.offset) context.tokens of
    [] => []
    first :: rest => [RefersTo (Between first.span.start
      (foldl (\end, token => token.span.finish) first.span.finish rest)) target]

mutual
  walk : Walker destination -> Environment destination -> Expr -> List (ReferenceTo destination)
  walk context env (NRef span name) =
    let target = case lexicalTarget name env of
          Just target => Just target
          Nothing => if any (\entry => fst entry == name) env then Nothing else context.globalTarget name
     in case (nameToken name span context.tokens, target) of
      (Just origin, Just target) => [RefersTo origin target]
      _ => []
  walk context env (NQualifiedRef region name) =
    case find (\token => token.kind == Name &&
                        token.span.start.offset >= region.start.offset &&
                        token.span.finish.offset <= region.finish.offset) (reverse context.tokens) of
      Just token => qualifierReferences context region token.span name ++
        (case context.qualifiedTarget name of
          Just target => [RefersTo token.span target]
          Nothing => [])
      Nothing => []
  walk context env (NSort _ _) = []
  walk context env (NUnitType _) = []
  walk context env (NUnitValue _) = []
  walk context env (NStringType _) = []
  walk context env (NStringValue _ _) = []
  walk context env (NNatValue _ _) = []
  walk context env (NBoolType _) = []
  walk context env (NBoolValue _ _) = []
  walk context env (NIf _ condition yes no) =
    walk context env condition ++ walk context env yes ++ walk context env no
  walk context env (NUnitCase _ value body) = walk context env value ++ walk context env body
  walk context env (NSigma span q r name domain body) =
    let target = binderToken name span domain context.tokens
     in walk context env domain ++ self context target ++ walk context ((name, map context.localTarget target) :: env) body
  walk context env (NRecType _ _) = []
  walk context env (NRecEnd _ _) = []
  walk context env (NRecMore _ _ _) = []
  walk context env (NRecFold _ _ _ _ _) = []
  walk context env (NSeqType _ _ _) = []
  walk context env (NSeqNil _ _) = []
  walk context env (NSeqCons _ _ _ _) = []
  walk context env (NSeqFold _ _ _ _ _) = []
  walk context env (NDataType _ _) = []
  walk context env (NDataCon _ _ _ _) = []
  walk context env (NNominalType _ _ _ _) = []
  walk context env (NNominalValue _ _ _) = []
  walk context env (NNominalCase _ _ _ _) = []
  walk context env (NVariantType _ _) = []
  walk context env (NVariantValue _ _ _ _) = []
  walk context env (NVariantCase _ _ _ _) = []
  walk context env (NBoxType _ _ ty) = walk context env ty
  walk context env (NBoxValue _ ty value) = walk context env ty ++ walk context env value
  walk context env (NBoxCase _ motive value branch) = walk context env motive ++ walk context env value ++ walk context env branch
  walk context env (NPairValue _ ty first second) = walk context env ty ++ walk context env first ++ walk context env second
  -- A final bare grouped-clause head may be a checked binder. This lexical
  -- traversal has no checking certificate, so suppress possible outer targets
  -- in its body rather than report an incorrect reference.
  walk context env (NEquationLambda _ [argument] _ (NDataCase _ value Nothing arms)) =
    if argument.spelling == "$clauseScrutinee"
    then walk context ((argument.spelling, Nothing) :: env) value ++
         walkDataArms True context ((argument.spelling, Nothing) :: env) arms
    else let scope = (argument.spelling, if argument.spelling == "_" then Nothing else Just (context.localTarget argument.span)) :: env
          in (if argument.spelling == "_" then [] else self context (Just argument.span)) ++
             walk context scope value ++ walkDataArms False context scope arms
  walk context env (NEquationLambda _ names _ body) =
    let sites = filter (\token => token.spelling /= "_" && token.spelling /= "$clauseScrutinee") names
        refs = concatMap (\token => self context (Just token.span)) sites
        following = foldl (\scope, token => (token.spelling, if token.spelling == "_" then Nothing else Just (context.localTarget token.span)) :: scope) env names
     in refs ++ walk context following body
  walk context env (NPatternLambda _ names body) =
    let sites = filter (\token => token.spelling /= "_") names
        refs = concatMap (\token => self context (Just token.span)) sites
        following = foldl (\scope, token => (token.spelling, if token.spelling == "_" then Nothing else Just (context.localTarget token.span)) :: scope) env names
     in refs ++ walk context following body
  walk context env (NDataCase _ value Nothing arms) = walk context env value ++ walkDataArms False context env arms
  walk context env (NDataCase _ value (Just motive) arms) = walk context env value ++ walk context env motive ++ walkDataArms False context env arms
  walk context env (NCaseEither _ asRecord _) = walk context env asRecord
  walk context env (NConstructorCase _ _ constructor value branch motive) =
    walk context env constructor ++ walk context env value ++ (case motive of Nothing => []; Just result => walk context env result) ++ walk context env branch
  walk context env (NInferCase _ _ value branch) = walk context env value ++ walk context env branch
  walk context env (NPairCase _ motive value branch) = walk context env motive ++ walk context env value ++ walk context env branch
  walk context env (NImplicitPi span q name domain body) =
    let target = binderToken name span domain context.tokens
     in walk context env domain ++ self context target ++ walk context ((name, map context.localTarget target) :: env) body
  walk context env (NConstraintPi span q name domain body) =
    let target = binderToken name span domain context.tokens
     in walk context env domain ++ self context target ++ walk context ((name, map context.localTarget target) :: env) body
  walk context env (NPi span q name domain body) =
    let target = binderToken name span domain context.tokens
     in walk context env domain ++ self context target ++ walk context ((name, map context.localTarget target) :: env) body
  walk context env (NLambda span q name domain body) =
    let target = binderToken name span domain context.tokens
     in walk context env domain ++ self context target ++ walk context ((name, map context.localTarget target) :: env) body
  walk context env (NImplementationApply _ _ function) = walk context env function
  walk context env (NDictionaryApply _ _ function argument) = walk context env function ++ (case argument of Nothing => []; Just value => walk context env value)
  walk context env (NInfix _ function left right) = walk context env left ++ walk context env function ++ walk context env right
  walk context env (NApply _ function argument) = walk context env function ++ walk context env argument
  walk context env (NImplicitApply _ function argument) = walk context env function ++ walk context env argument
  walk context env (NSequence _ first rest) = walk context env first ++ walk context env rest
  walk context env (NDoBind span name domain action body) =
    let target = binderToken name span domain context.tokens
     in walk context env domain ++ walk context env action ++ self context target ++
        walk context ((name, map context.localTarget target) :: env) body
  walk context env (NDoResult _ result body) = walk context env result ++ walk context env body
  walk context env (NAscribe _ term expected) = walk context env term ++ walk context env expected
  walk context env (NLet span q name domain value body) =
    let target = binderToken name span domain context.tokens
     in walk context env domain ++ walk context env value ++ self context target ++
        walk context ((name, map context.localTarget target) :: env) body

  walkDataArms : Bool -> Walker destination -> Environment destination -> List (Token, List Token, Expr) -> List (ReferenceTo destination)
  walkDataArms clause context env [] = []
  walkDataArms clause context env ((constructor, binder, body) :: rest) =
    let qualified = elem '.' (unpack constructor.spelling)
        selected : Maybe destination
        selected = if qualified then context.qualifiedTarget constructor.spelling else case lexicalTarget constructor.spelling env of
          Just local => Just local
          Nothing => if any (\entry => fst entry == constructor.spelling) env then Nothing else context.globalTarget constructor.spelling
        origin : Maybe SourceSpan
        origin = if qualified then map (\token => token.span) (find (\token => token.kind == Name &&
                    token.span.start.offset >= constructor.span.start.offset &&
                    token.span.finish.offset <= constructor.span.finish.offset) (reverse context.tokens))
                 else Just constructor.span
        refs : List (ReferenceTo destination)
        refs = if clause && null rest && null binder then [] else
          case (origin, selected) of (Just region, Just dest) => [RefersTo region dest]; _ => []
        qualifierRefs : List (ReferenceTo destination)
        qualifierRefs = if qualified then case origin of
          Just region => qualifierReferences context constructor.span region constructor.spelling
          Nothing => []
          else []
        binderRefs : List (ReferenceTo destination)
        binderRefs = concatMap (\bound => if bound.spelling == "_" then [] else self context (Just bound.span)) binder
        following : Environment destination
        following = foldl (\scope, bound => (bound.spelling, if bound.spelling == "_" then Nothing else Just (context.localTarget bound.span)) :: scope) env binder
        bodyScope = if clause && null rest && null binder
                    then (constructor.spelling, Nothing) :: following else following
     in refs ++ qualifierRefs ++ binderRefs ++ walk context bodyScope body ++ walkDataArms clause context env rest

dataParameters : Walker destination -> Environment destination -> List RecordParameter ->
                 (List (ReferenceTo destination), Environment destination)
dataParameters context env [] = ([], env)
dataParameters context env (parameter :: rest) =
  let target = binderToken parameter.name parameter.span parameter.domain context.tokens
      following = (parameter.name, map context.localTarget target) :: env
      (refs, scope) = dataParameters context following rest
   in (walk context env parameter.domain ++ self context target ++ refs, scope)

dataFields : Walker destination -> Environment destination -> List RecordField ->
             (List (ReferenceTo destination), Environment destination)
dataFields context env [] = ([], env)
dataFields context env (field :: rest) =
  let following = (field.token.spelling, Just (context.localTarget field.token.span)) :: env
      (refs, scope) = dataFields context following rest
   in (walk context env field.ty ++ self context (Just field.token.span) ++ refs, scope)

-- Each lowered arm retains its authored constructor token. The immediately
-- preceding token is its clause header, as guaranteed by clause parsing.
clauseHeaders : Walker destination -> Declaration -> List (ReferenceTo destination)
clauseHeaders context decl = case decl.value of
  NEquationLambda _ [argument] _ (NDataCase _ _ Nothing arms) =>
    if argument.spelling == "$clauseScrutinee" then concatMap header arms else []
  _ => []
  where
    header : (Token, List Token, Expr) -> List (ReferenceTo destination)
    header (constructor, _, _) =
      case find (\token => token.span.finish.offset <= constructor.span.start.offset && token.kind /= OpenParen) (reverse context.tokens) of
        Just token => if token.kind == Name && token.spelling == decl.name &&
                         token.span.start.line == constructor.span.start.line &&
                         token.span.start.offset /= decl.definitionNameSpan.start.offset
          then [RefersTo token.span (context.localTarget decl.definitionNameSpan)] else []
        Nothing => []

declarations : Walker destination -> Environment destination -> List AuthoredDeclaration -> List (ReferenceTo destination)
declarations context env [] = []
declarations context env (MutualItem group :: rest) =
  let members = group.first :: group.second :: group.others
      scope = foldl (\scope, decl => (decl.name, Just (context.localTarget decl.definitionNameSpan)) :: scope) env members
      refs = concatMap (\decl =>
        [RefersTo decl.nameSpan (context.localTarget decl.definitionNameSpan),
         RefersTo decl.definitionNameSpan (context.localTarget decl.definitionNameSpan)] ++
        walk context env decl.expected ++ walk context scope decl.value) members
   in refs ++ declarations context scope rest

declarations context env (Ordinary decl :: rest) =
  (if decl.name == "_" then [] else if decl.generated then
    [RefersTo decl.nameSpan (context.localTarget decl.definitionNameSpan)] else
    [RefersTo decl.nameSpan (context.localTarget decl.definitionNameSpan),
     RefersTo decl.definitionNameSpan (context.localTarget decl.definitionNameSpan)]) ++
  (if decl.generated then [] else clauseHeaders context decl ++ walk context env decl.expected ++ walk context env decl.value) ++
  declarations context ((decl.name, Just (context.localTarget decl.definitionNameSpan)) :: env) rest

declarations context env (ImplementationBlock block :: rest) =
  [RefersTo block.name.span (context.localTarget block.name.span)] ++
  walk context env block.target ++
  (let (params, _) = implementationTelescope block.target
       scope = foldl (\scope, parameter =>
         (parameter.name, map context.localTarget (binderToken parameter.name parameter.span parameter.domain context.tokens)) :: scope) env params
    in concatMap (\method => walk context scope method.value) block.methods) ++
  declarations context ((block.name.spelling, Just (context.localTarget block.name.span)) :: env) rest

declarations context env (ImplementationItem decl :: rest) =
  (if decl.name == "_" then [] else if decl.generated then
    [RefersTo decl.nameSpan (context.localTarget decl.definitionNameSpan)] else
    [RefersTo decl.nameSpan (context.localTarget decl.definitionNameSpan),
     RefersTo decl.definitionNameSpan (context.localTarget decl.definitionNameSpan)]) ++
  (if decl.generated then [] else walk context env decl.expected ++ walk context env decl.value) ++
  declarations context ((decl.name, Just (context.localTarget decl.definitionNameSpan)) :: env) rest

declarations context env (item@(DataItem sourceData) :: rest) =
  let sites = bindingSites item
      refs = map (\site => RefersTo site.nameSpan (context.localTarget site.definitionNameSpan)) sites
      following = foldl (\scope, site => (site.name, Just (context.localTarget site.definitionNameSpan)) :: scope) env sites
      (paramRefs, paramScope) = dataParameters context following sourceData.params
      ctorRefs = concatMap (\ctor => let (fieldRefs, scope) = dataFields context paramScope ctor.fields
                                     in fieldRefs ++ walk context scope ctor.result) sourceData.constructors
   in refs ++ paramRefs ++ ctorRefs ++ declarations context following rest

declarations context env (item@(RecordItem authored) :: rest) =
  let sites = bindingSites item
      refs = map (\site => RefersTo site.nameSpan (context.localTarget site.definitionNameSpan)) sites
      following = foldl (\scope, site => (site.name, Just (context.localTarget site.definitionNameSpan)) :: scope) env sites
      (paramRefs, paramScope) = dataParameters context env authored.params
      (fieldRefs, _) = dataFields context paramScope authored.fields
   in refs ++ paramRefs ++ fieldRefs ++ declarations context following rest

declarations context env (item@(InterfaceItem authored) :: rest) =
  let sites = bindingSites item
      refs = map (\site => RefersTo site.nameSpan (context.localTarget site.definitionNameSpan)) sites
      following = foldl (\scope, site => (site.name, Just (context.localTarget site.definitionNameSpan)) :: scope) env sites
      (paramRefs, paramScope) = dataParameters context env authored.params
      (fieldRefs, _) = dataFields context paramScope authored.fields
   in refs ++ paramRefs ++ fieldRefs ++ declarations context following rest

||| Shared traversal with optional checked module targets for qualified AST nodes.
public export
documentReferencesWithModules : (SourceSpan -> destination) -> (String -> Maybe destination) ->
                               (String -> Maybe destination) -> (String -> Maybe destination) ->
                               ParsedDocument -> List (ReferenceTo destination)
documentReferencesWithModules local globals qualified modules document =
  let context = Walking document.tokens local qualified globals modules
   in case document.body of
        EmptyDocument => []
        DeclarationDocument values => declarations context [] values
        ExpressionDocument value => walk context [] value

||| Lexical clients do not infer module targets without a checked module graph.
public export
documentReferencesWithGlobals : (SourceSpan -> destination) -> (String -> Maybe destination) ->
                               (String -> Maybe destination) -> ParsedDocument ->
                               List (ReferenceTo destination)
documentReferencesWithGlobals local globals qualified =
  documentReferencesWithModules local globals qualified (const Nothing)

||| Shared traversal over parsed data, not a checking certificate.
public export
documentReferencesUsing : (SourceSpan -> destination) -> (String -> Maybe destination) ->
                          ParsedDocument -> List (ReferenceTo destination)
documentReferencesUsing local qualified document =
  documentReferencesWithGlobals local (const Nothing) qualified document

||| Source-order, nonrecursive declarations and nearest lexical binders only.
||| Unresolved/prelude names have no local target. No type-checking claim.
public export
documentReferences : String -> Either SymbolError (List Reference)
documentReferences source = do
  document <- parseDocument 64 256 source
  Right (documentReferencesUsing id (const Nothing) document)

contains : Nat -> Nat -> SourceSpan -> Bool
contains line column span = line == span.start.line &&
  column >= span.start.column && column < span.finish.column

sameTarget : SourceSpan -> SourceSpan -> Bool
sameTarget left right = left.start.offset == right.start.offset &&
                        left.finish.offset == right.finish.offset

sourceOrder : SourceSpan -> SourceSpan -> Ordering
sourceOrder left right = compare left.start.offset right.start.offset

||| Include declaration sites and uses of the same lexical target, in source order.
||| Top-level signature/definition headers count as declaration sites.
||| Unknown/prelude names and punctuation return an empty list, not text matches.
public export
referencesAt : String -> Nat -> Nat -> Either SymbolError (List SourceSpan)
referencesAt source line column = do
  references <- documentReferences source
  case find (\reference => contains line column reference.origin) references of
    Nothing => Right []
    Just selected => Right (sortBy sourceOrder (map origin
      (filter (\reference => sameTarget reference.target selected.target) references)))

||| One-based scalar line/column; punctuation, whitespace, and unknown names miss.
public export
definitionAt : String -> Nat -> Nat -> Either SymbolError (Maybe SourceSpan)
definitionAt source line column = do
  references <- documentReferences source
  Right (map target (find (\reference => contains line column reference.origin) references))
