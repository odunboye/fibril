-- Checked closed module interfaces, not opaque globals or project editor reports.
module Fibril.Driver.ModuleCheck

import Data.List
import Data.List1
import Data.String
import Data.Vect
import Fibril.Core.Quantity
import Fibril.Core.Size
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Runtime
import Fibril.Core.Erased
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Pretty
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Document
import Fibril.Source.Declaration
import Fibril.Elaboration.Declaration
import Fibril.Elaboration.Interface
import Fibril.Elaboration.DataSchema
import Fibril.Source.Global
import Fibril.Elaboration.Expression
import Fibril.Elaboration.Expression.Scope
import Fibril.Elaboration.Expression.Constructor
import Fibril.Elaboration.Expression.Parameters
import Fibril.Driver.Limits
import Fibril.Driver.Check
import Fibril.Driver.Prelude
import Fibril.Driver.ModuleGraph

%default total

nodes : Term n -> Nat
nodes = coreNodes

record Weighted where
  constructor Weight
  global : GlobalDefinition
  size : Nat

weighted : GlobalDefinition -> Weighted
weighted global = Weight global (3 + nodes global.declaredType + nodes global.value)

referenceImplicit : List Weighted -> String -> Nat
referenceImplicit [] name = 0
referenceImplicit (entry :: rest) name =
  if entry.global.name == name then entry.global.implicitPrefix else referenceImplicit rest name

implicitHeadCost : List Weighted -> List String -> Expr -> Nat
implicitHeadCost globals env (NRef _ name) =
  if elem name env then 0 else referenceImplicit globals name
implicitHeadCost globals env (NQualifiedRef _ name) = referenceImplicit globals name
implicitHeadCost globals env _ = 0

implicitSpineCount : List Weighted -> List String -> Expr -> Nat
implicitSpineCount globals env (NApply _ function _) = implicitSpineCount globals env function
implicitSpineCount globals env (NImplicitApply _ function _) = implicitSpineCount globals env function
implicitSpineCount globals env head = implicitHeadCost globals env head

spineBraceCount : Expr -> Nat
spineBraceCount (NApply _ function _) = spineBraceCount function
spineBraceCount (NImplicitApply _ function _) = S (spineBraceCount function)
spineBraceCount _ = 0

spineOrdinaryCount : Expr -> Nat
spineOrdinaryCount (NApply _ function _) = S (spineOrdinaryCount function)
spineOrdinaryCount (NImplicitApply _ function _) = spineOrdinaryCount function
spineOrdinaryCount _ = 0

implicitBodyCount : List Weighted -> List String -> Expr -> Nat
implicitBodyCount globals env expression@(NApply _ _ _) = implicitSpineCount globals env expression
implicitBodyCount globals env expression@(NImplicitApply _ _ _) = implicitSpineCount globals env expression
implicitBodyCount _ _ _ = 0

validImplicitPrefix : Bool -> Nat -> Term n -> Bool
validImplicitPrefix allowImplicitOnly Z (Pi _ _ _) = True
validImplicitPrefix allowImplicitOnly Z _ = allowImplicitOnly
validImplicitPrefix allowImplicitOnly (S count) (Pi Erased _ rest) = validImplicitPrefix allowImplicitOnly count rest
validImplicitPrefix _ _ _ = False

referenceCost : List Weighted -> String -> Nat
referenceCost [] name = 1
referenceCost (entry :: rest) name =
  if entry.global.name == name then entry.size else referenceCost rest name

providerCost : List Weighted -> Nat
providerCost [] = 0
providerCost (entry :: rest) = case entry.global.provider of
  Nothing => providerCost rest
  Just _ => max entry.size (providerCost rest)

-- Conservative elaboration size before any global is renamed/cloned. Counts
-- annotations and identity ascriptions; saturation avoids huge intermediate costs.
mutual
  cost : Nat -> List Weighted -> List String -> Expr -> Nat
  cost limit globals env expression = min (S limit) $ case expression of
    NRef _ name => if elem name env then 1 else referenceCost globals name
    NQualifiedRef _ name => referenceCost globals name
    NSort _ _ => 1
    NUnitType _ => 1
    NUnitValue _ => 1
    NBoolType _ => 1
    NBoolValue _ _ => 1
    NStringType _ => 1
    NStringValue _ _ => 1
    NIf _ c t e => 1 + cost limit globals env c + cost limit globals env t + cost limit globals env e
    NUnitCase _ a b => 1 + cost limit globals env a + cost limit globals env b
    NSigma _ _ _ name a b => 1 + cost limit globals env a + cost limit globals (name :: env) b
    NPairValue _ ty a b => 1 + cost limit globals env ty + cost limit globals env a + cost limit globals env b
    NNominalType _ _ indices shape => 1 + listCost limit globals env indices + cost limit globals env shape
    NNominalValue _ ty value => 1 + cost limit globals env ty + cost limit globals env value
    NNominalCase _ p value branch => 1 + cost limit globals env p + cost limit globals env value + cost limit globals env branch
    NVariantType _ arms => 1 + armsCost limit globals env arms
    NVariantValue _ ty _ payload => 1 + cost limit globals env ty + (case payload of Nothing => 0; Just value => cost limit globals env value)
    NVariantCase _ p value branches => 1 + cost limit globals env p + cost limit globals env value + listCost limit globals env branches
    NBoxType _ _ a => 1 + cost limit globals env a
    NBoxValue _ a b => 1 + cost limit globals env a + cost limit globals env b
    NBoxCase _ a b c => 1 + cost limit globals env a + cost limit globals env b + cost limit globals env c
    NEquationLambda _ names signature body =>
      min (S limit) (1 + length names * 513 + cost limit globals env signature + cost limit globals (reverse (map spelling names) ++ env) body)
    NPatternLambda _ names body => 4 + 2 * inferredFieldNodes + cost limit globals (reverse (map spelling names) ++ env) body
    NDataCase _ value motive branches =>
      let copies : Nat = case motive of Nothing => 4; Just _ => 1 in
        min (S limit) (4096 + cost limit globals env value +
          (case motive of
            Nothing => 2048 + 2 * (1 + 512 + inferredResultNodes)
            Just explicit => 2 * cost limit globals env explicit) +
          dataArmsCost limit globals env copies branches)
    NConstructorCase _ _ constructor value branch motive =>
      8 + 3 * inferredParameterNodes + 3 * cost limit globals env constructor + cost limit globals env value + 2 * cost limit globals env branch +
        (case motive of Nothing => inferredResultNodes; Just explicit => cost limit globals env explicit)
    NInferCase _ _ value branch => 8 + cost limit globals env value + 2 * cost limit globals env branch + inferredResultNodes
    NPairCase _ motive value branch => 1 + cost limit globals env motive + cost limit globals env value + cost limit globals env branch
    NImplicitPi _ _ name a b => 1 + cost limit globals env a + cost limit globals (name :: env) b
    NConstraintPi _ _ name a b => 1 + cost limit globals env a + cost limit globals (name :: env) b
    NImplementationApply _ _ function => 1 + cost limit globals env function + providerCost globals
    NDictionaryApply _ _ function argument => 2 + cost limit globals env function + (case argument of Nothing => 1; Just value => cost limit globals env value)
    NPi _ _ name a b => 1 + cost limit globals env a + cost limit globals (name :: env) b
    NLambda _ _ name a b => 1 + cost limit globals env a + cost limit globals (name :: env) b
    NInfix _ function left right => 2 + cost limit globals env function + cost limit globals env left + cost limit globals env right
    NApply _ a b =>
      let capacity = implicitSpineCount globals env a
          needsInference = capacity > 0 && spineBraceCount a < capacity
          firstOrdinary = spineOrdinaryCount a == 0 in
        1 + cost limit globals env a + cost limit globals env b +
        (if needsInference then implicitProposalDepth * 513 else 0) +
        (if needsInference && firstOrdinary then 1025 + capacity * 513 else 0)
    NImplicitApply _ a b => 1 + cost limit globals env a + cost limit globals env b
    NAscribe _ a b => 3 + cost limit globals env a + cost limit globals env b
    NLet _ _ name a value body =>
      let implicitBody = implicitBodyCount globals (name :: env) body > 0 in
        (if wantsExpected body || implicitBody then 514 else 2) + cost limit globals env a + cost limit globals env value +
        cost limit globals (name :: env) body
    NSequence _ a b => 7 + cost limit globals env a + cost limit globals env b
    NDoBind _ name a action body => 3 + 2 * cost limit globals env a + cost limit globals env action +
                                    cost limit globals (name :: env) body
    NDoResult _ result body =>
      let resultSize = cost limit globals env result
       in 4 + resultSize + resultSize * cost limit globals env body

  -- Count each source arm once, then reserve its potential weakened copies.
  -- Re-traversing nested case bodies per copy would make admission exponential.
  dataArmsCost : Nat -> List Weighted -> List String -> Nat -> List (Token, Maybe Token, Expr) -> Nat
  dataArmsCost limit globals env copies [] = 0
  dataArmsCost limit globals env copies ((_, binder, body) :: rest) =
    let branch = cost limit globals (maybe env (\token => token.spelling :: env) binder) body in
      min (S limit) (1025 + copies * (513 + branch) + dataArmsCost limit globals env copies rest)

  listCost : Nat -> List Weighted -> List String -> List Expr -> Nat
  listCost limit globals env [] = 0
  listCost limit globals env (x :: xs) = min (S limit) (1 + cost limit globals env x + listCost limit globals env xs)

  armsCost : Nat -> List Weighted -> List String -> List (Maybe (Quantity, Expr)) -> Nat
  armsCost limit globals env [] = 0
  armsCost limit globals env (Nothing :: xs) = min (S limit) (1 + armsCost limit globals env xs)
  armsCost limit globals env (Just (_, ty) :: xs) = min (S limit) (1 + cost limit globals env ty + armsCost limit globals env xs)


record Interface where
  constructor Exports
  name : List String
  bindings : List Weighted
  schemas : List InterfaceSchema
  dataSchemas : List DataSchema

record Compiled where
  constructor Definitions
  locals : List Weighted
  exports : List Weighted
  remaining : Nat

public export
record CheckedProject where
  constructor Project
  graph : ModuleGraph
  term : Term 0
  inferredType : Term 0

problem : ModuleSnapshot -> Maybe Position -> String -> GraphError
problem snapshot point message =
  DetailedGraphFailure snapshot.path snapshot.source point message True Nothing "module-checking"

moduleText : List String -> String
moduleText names = concat (intersperse "." names)

resolve : ModuleSnapshot -> List Weighted -> Expr -> Either GraphError (Term 0)
resolve snapshot globals expression = case elaborateClosedWith (map global globals) expression of
  Left err => Left ({ stage := if err.elaborating then "elaboration" else "resolution" } (problem snapshot (Just err.position) (show err)))
  Right term => Right term

-- This points to the real checked declaration, not the unknown failing subterm.
declarationFailure : ModuleSnapshot -> Declaration -> String -> String -> String -> GraphError
declarationFailure snapshot decl stage label detail =
  { stage := stage } (problem snapshot (Just decl.nameSpan.start)
    (label ++ " While checking " ++ (if decl.generated then "generated declaration " else "declaration ") ++
      show decl.name ++ " (declaration-level location): " ++ detail))

-- True identifies a closed dictionary value; factories are explicit-only.
dictionarySignature : Nat -> Term n -> Either String Bool
dictionarySignature Z ty = Left "Implementation signature checking depth exhausted"
dictionarySignature (S depth) ty = case weakHead typeReductionFuel ty of
  HeadLimit _ => Left "Implementation dictionary type reduction budget exhausted"
  HeadForm (BoxType _ _) => Right True
  HeadForm (Sigma _ _ _ _) => Right True
  HeadForm (Pi q domain result) => do
    if q == Erased then Right () else case weakHead typeReductionFuel domain of
      HeadForm (BoxType _ _) => Right ()
      HeadForm (Sigma _ _ _ _) => Right ()
      HeadLimit _ => Left "Implementation factory parameter type reduction budget exhausted"
      _ => Left "Runtime implementation factory parameters must be dictionary-shaped"
    _ <- dictionarySignature depth result
    Right False
  HeadForm _ => Left "Implementation signature must be a dictionary-shaped unary or dependent-pair type, or a factory returning one"

compileDeclarations : ModuleSnapshot -> List String -> List Weighted -> List Declaration -> Nat ->
                      Either GraphError Compiled
compileDeclarations snapshot name globals [] remaining = Right (Definitions [] [] remaining)
compileDeclarations snapshot name globals (decl :: rest) remaining = do
  if decl.quantity == Linear || decl.name == "_"
     then Left (problem snapshot (Just decl.nameSpan.start)
                "Module globals require erased/unrestricted quantities and referenceable names")
     else Right ()
  if decl.dictionary && decl.quantity /= Unrestricted
     then Left (problem snapshot (Just decl.nameSpan.start) "Implementations require unrestricted named dictionary values") else Right ()
  let estimate = cost remaining globals [] decl.expected + cost remaining globals [] decl.value
  if estimate > remaining then Left (problem snapshot (Just decl.nameSpan.start)
                                     "Expanded core construction budget exhausted (200000)")
     else Right ()
  let implicitPrefix = implicitPrefixCount decl.expected
  if implicitPrefix > 64 then Left (problem snapshot (Just decl.nameSpan.start) "Implicit telescope admission exhausted (64)") else Right ()
  ty <- case elaborateSignatureWith decl.generated (map global globals) (Just Empty) [] decl.expected of
    Left err => Left ({ stage := if err.elaborating then "elaboration" else "resolution" } (problem snapshot (Just err.position) (show err)))
    Right ty => Right ty
  if implicitPrefix > 0 && not (validImplicitPrefix decl.generated implicitPrefix ty)
    then Left (problem snapshot (Just decl.nameSpan.start) "Implicit metadata does not match an erased leading Pi prefix followed by an explicit Pi")
    else Right ()
  value <- case elaborateExpected (map global globals) Empty [] ty decl.value of
    Left err => Left ({ stage := if err.elaborating then "elaboration" else "resolution" } (problem snapshot (Just err.position) (show err)))
    Right value => Right value
  if nodes ty + nodes value > estimate
     then Left (problem snapshot Nothing "Internal module expansion estimate was insufficient")
     else Right ()
  case decl.quantity of
    Erased => case checkErased checkingDepth typeReductionFuel Empty value ty of
      Left err => Left (declarationFailure snapshot decl "erased-checking" "Module erased checking:" (show err))
      Right () => Right ()
    _ => case checkRuntime checkingDepth typeReductionFuel Empty value ty of
      Left err => Left (declarationFailure snapshot decl "runtime-checking" "Module checking:" (show err))
      Right _ => Right ()
  provider <- if decl.dictionary then case dictionarySignature checkingDepth ty of
    Right closed => Right closed
    Left message => Left ({ stage := "runtime-checking" } (problem snapshot (Just decl.nameSpan.start) message))
    else Right False
  let identity = moduleText name ++ "." ++ decl.name
  let definition = GlobalEntry (if provider then Just identity else Nothing) implicitPrefix decl.quantity decl.name ty value
  let local = weighted definition
  let qualified = Weight ({ name := identity } definition) local.size
  following <- compileDeclarations snapshot name (local :: qualified :: globals) rest (minus remaining estimate)
  Right (Definitions (local :: following.locals)
           (if decl.exported then qualified :: following.exports else following.exports) following.remaining)

directImports : ModuleSnapshot -> List Interface -> Either GraphError (List Weighted)
directImports snapshot interfaces = collect [] snapshot.document.imports
  where
    collect : List (List String) -> List ImportDeclaration -> Either GraphError (List Weighted)
    collect seen [] = Right []
    collect seen (dependency :: rest) =
      if elem dependency.components seen then collect seen rest else
        case find (\entry => entry.name == dependency.components) interfaces of
          Nothing => Left (problem snapshot (Just dependency.span.start) "Missing checked dependency interface")
          Just entry => (entry.bindings ++) <$> collect (dependency.components :: seen) rest

-- Add a short name only when exactly one direct import exports it.  Keep the
-- qualified entry as the authority, and do not register aliases as providers.
shortName : String -> String
shortName name = case reverse (forget (Data.String.split (== '.') name)) of
  [] => name
  part :: _ => part

importAliases : List Weighted -> List Weighted
importAliases imported = mapMaybe alias groups
  where
    named : List (String, Weighted)
    named = map (\entry => (shortName entry.global.name, entry)) imported
    groups : List (List1 (String, Weighted))
    groups = groupBy (\a, b => fst a == fst b) (sortBy (\a, b => compare (fst a) (fst b)) named)
    alias : List1 (String, Weighted) -> Maybe Weighted
    alias ((name, entry) ::: []) = Just ({ global := { name := name, provider := Nothing } entry.global } entry)
    alias _ = Nothing

directSchemas : ModuleSnapshot -> List Interface -> List InterfaceSchema
directSchemas snapshot interfaces = concatMap (\dependency =>
  case find (\entry => entry.name == dependency.components) interfaces of
    Nothing => []
    Just entry => entry.schemas) snapshot.document.imports

elaborateAt : ModuleSnapshot -> List InterfaceSchema -> List AuthoredDeclaration -> Either GraphError (List Declaration)
elaborateAt snapshot schemas authored = case elaborateDeclarationsIn
  (map (\header => moduleText header.components) snapshot.document.moduleHeader) schemas 64 authored of
  Left err => Left ({ stage := "elaboration" } (problem snapshot (Just err.position) err.message))
  Right declarations => Right declarations

anonymous : ModuleSnapshot -> List InterfaceSchema -> List Weighted -> Nat -> Either GraphError (Term 0)
anonymous snapshot schemas globals remaining = do
  expression <- case snapshot.document.body of
    EmptyDocument => Left (problem snapshot Nothing "Entry requires an expression or main")
    ExpressionDocument expression => Right expression
    DeclarationDocument authored => do
      declarations <- elaborateAt snapshot schemas authored
      if any (\decl => decl.name == "main") declarations
         then Right (lowerDeclarations snapshot.document.end declarations)
         else Left (problem snapshot Nothing "Entry requires a main definition")
  if cost remaining globals [] expression > remaining
     then Left (problem snapshot Nothing "Expanded core construction budget exhausted (200000)")
     else do
       term <- resolve snapshot globals expression
       if nodes term > cost remaining globals [] expression
          then Left (problem snapshot Nothing "Internal entry expansion estimate was insufficient")
          else Right term

compileGraph : Bool -> ModuleGraph -> List Weighted -> List Interface -> Nat -> List ModuleSnapshot ->
               Either GraphError (Maybe CheckedProject)
compileGraph requireEntry graph prelude interfaces remaining [] =
  if requireEntry then Left (GraphFailure graph.entry "" Nothing "No entry snapshot in graph") else Right Nothing
compileGraph requireEntry graph prelude interfaces remaining (snapshot :: rest) = do
  if requireEntry && snapshot.path == graph.entry && not (null rest)
     then Left (problem snapshot Nothing "Entry snapshot must be last in dependency order")
     else Right ()
  imported <- directImports snapshot interfaces
  let aliases = importAliases imported
  let qualifiedSchemas = directSchemas snapshot interfaces
  let schemas = qualifiedSchemas ++ mapMaybe (\schema =>
        if any (\entry => entry.global.name == shortName schema.name) aliases
          then Just ({ name := shortName schema.name } schema) else Nothing) qualifiedSchemas
  -- Imports shadow Prelude names; ambiguous imports must not silently fall
  -- back to a Prelude definition. Local declarations are prepended later.
  let visiblePrelude = filter (\entry => not (any (\item => shortName item.global.name == entry.global.name) imported)) prelude
  let globals = imported ++ aliases ++ visiblePrelude
  case snapshot.document.moduleHeader of
    Nothing => if not requireEntry || snapshot.path /= graph.entry then Left (problem snapshot Nothing "Anonymous dependency") else do
      term <- anonymous snapshot schemas globals remaining
      case inferRuntime checkingDepth typeReductionFuel Empty term of
        Left err => Left ({ stage := "runtime-checking" } (problem snapshot Nothing ("Entry checking: " ++ show err)))
        Right checked => Right (Just (Project graph term checked.inferredType))
    Just header => do
      if any (\entry => entry.name == header.components) interfaces
         then Left (problem snapshot (Just header.nameSpan.start) "Duplicate checked module identity")
         else Right ()
      declarations <- case snapshot.document.body of
        DeclarationDocument authored => elaborateAt snapshot schemas authored
        EmptyDocument => Right []
        _ => Left (problem snapshot Nothing "Named modules require declarations")
      compiled <- compileDeclarations snapshot header.components globals declarations remaining
      case graph.scope of
        PackageRoots _ _ => if header.components == ["Main"] then do
          main <- case find (\entry => entry.global.name == "main") compiled.locals of
            Nothing => Left (problem snapshot Nothing "Application entry requires its own main definition")
            Just main => Right main
          if main.global.quantity == Unrestricted then Right () else Left (problem snapshot Nothing "Application main must be unrestricted")
          else Right ()
        SingleRoot => Right ()
      if requireEntry && snapshot.path == graph.entry
         then do
            main <- case find (\entry => entry.global.name == "main") compiled.locals of
              Nothing => Left (problem snapshot Nothing "Entry module requires its own main definition")
              Just entry => Right entry
            if main.global.quantity /= Unrestricted
               then Left (problem snapshot Nothing "Entry main must be unrestricted, not erased")
               else Right ()
            if main.size > compiled.remaining
               then Left (problem snapshot Nothing "Expanded core construction budget exhausted (200000)")
               else Right ()
            term <- case lookupGlobal "main" [main.global] of
              Nothing => Left (problem snapshot Nothing "Missing main binding")
              Just term => Right term
            case inferRuntime checkingDepth typeReductionFuel Empty term of
              Left err => Left ({ stage := "runtime-checking" } (problem snapshot Nothing ("Entry checking: " ++ show err)))
              Right checked => Right (Just (Project graph term checked.inferredType))
         else let visible = case snapshot.document.body of
                    DeclarationDocument authored => exportedSchemas (moduleText header.components) authored
                    _ => []
               in let dataHints = case snapshot.document.body of
                        DeclarationDocument authored => exportedDataSchemas (moduleText header.components) authored
                        _ => []
                   in compileGraph requireEntry graph prelude (Exports header.components compiled.exports visible dataHints :: interfaces)
                           compiled.remaining rest

||| Check every dependency declaration before exposing its qualified exports.
||| Expansion budget concerns elaboration, not normalization/allocation/time bounds.
public export
checkModuleGraph : ModuleGraph -> Either GraphError CheckedProject
checkModuleGraph graph = do
  prelude <- case preludeGlobals of
    Left err => Left ({ stage := "prelude" } (GraphFailure graph.entry "" Nothing ("Bundled prelude: " ++ err)))
    Right globals => Right (map weighted globals)
  checked <- compileGraph True graph prelude [] 200000 graph.modules
  case checked of
    Just project => Right project
    Nothing => Left (GraphFailure graph.entry "" Nothing "Missing checked entry")

public export
checkInventoryGraph : ModuleGraph -> Either GraphError ()
checkInventoryGraph graph = do
  prelude <- case preludeGlobals of
    Left err => Left (GraphFailure graph.root "" Nothing (show err))
    Right globals => Right (map weighted globals)
  _ <- compileGraph False graph prelude [] 200000 graph.modules
  Right ()

public export
data ProjectOutcome
  = GraphUnavailable GraphError
  | ProjectRejected ModuleGraph GraphError
  | ProjectAccepted CheckedProject

||| Preserve loaded snapshots on a checking failure for source-aware consumers.
public export
prepareProject : String -> String -> IO ProjectOutcome
prepareProject root entry = do
  loaded <- loadModuleGraph root entry
  pure $ case loaded of
    Left err => GraphUnavailable err
    Right graph => case checkModuleGraph graph of
      Left err => ProjectRejected graph err
      Right project => ProjectAccepted project

public export
checkProject : String -> String -> IO (Either GraphError CheckedProject)
checkProject root entry = do
  outcome <- prepareProject root entry
  pure $ case outcome of
    GraphUnavailable err => Left err
    ProjectRejected _ err => Left err
    ProjectAccepted project => Right project

||| Local package closure loading still passes the ordinary independent checker.
public export
checkPackage : String -> IO (Either GraphError CheckedProject)
checkPackage manifest = do
  loaded <- loadPackageModuleGraph manifest
  pure (loaded >>= checkModuleGraph)

public export
projectReport : CheckedProject -> List String
projectReport project =
  ["Module checking: accepted (closed transparent globals)",
   "Modules: " ++ show (length project.graph.modules),
   "Type: " ++ renderType project.inferredType]

public export
checkLocalPackage : String -> IO (Either GraphError (List String))
checkLocalPackage manifest = do
  loaded <- loadLocalPackageGraph CheckInventory manifest
  pure $ do
    graph <- loaded
    if graph.entry == "" then do
      checkInventoryGraph graph
      Right ["Library checking: accepted (no runtime entry)", "Modules: " ++ show (length graph.modules)]
       else projectReport <$> checkModuleGraph graph
