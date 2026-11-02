-- Checked closed module interfaces, not opaque globals or project editor reports.
module Fibril.Driver.ModuleCheck

import Data.List
import Fibril.Core.Quantity
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
nodes (Variable _) = 1
nodes (Universe _) = 1
nodes UnitType = 1
nodes UnitValue = 1
nodes BoolType = 1
nodes BoolTrue = 1
nodes BoolFalse = 1
nodes StringType = 1
nodes (StringValue _) = 1
nodes (StringAppend a b) = 1 + nodes a + nodes b
nodes (StringEqual a b) = 1 + nodes a + nodes b
nodes (BoxType _ a) = 1 + nodes a
nodes (BoxValue a b) = 1 + nodes a + nodes b
nodes (BoxCase a b c) = 1 + nodes a + nodes b + nodes c
nodes (IOType a) = 1 + nodes a
nodes (IOPure a) = 1 + nodes a
nodes (WriteLine a) = 1 + nodes a
nodes (IOBind a b c d) = 1 + nodes a + nodes b + nodes c + nodes d
nodes (BoolCase a b c) = 1 + nodes a + nodes b + nodes c
nodes (Sigma _ _ a b) = 1 + nodes a + nodes b
nodes (PairCase motive value branch) = 1 + nodes motive + nodes value + nodes branch
nodes (PairValue ty a b) = 1 + nodes ty + nodes a + nodes b
nodes (Pi _ a b) = 1 + nodes a + nodes b
nodes (Lambda _ a b) = 1 + nodes a + nodes b
nodes (Apply a b) = 1 + nodes a + nodes b
nodes (UnitCase a b) = 1 + nodes a + nodes b

record Weighted where
  constructor Weight
  global : GlobalDefinition
  size : Nat

weighted : GlobalDefinition -> Weighted
weighted global = Weight global (3 + nodes global.declaredType + nodes global.value)

referenceCost : List Weighted -> String -> Nat
referenceCost [] name = 1
referenceCost (entry :: rest) name =
  if entry.global.name == name then entry.size else referenceCost rest name

-- Conservative elaboration size before any global is renamed/cloned. Counts
-- annotations and identity ascriptions; saturation avoids huge intermediate costs.
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
  NBoxType _ _ a => 1 + cost limit globals env a
  NBoxValue _ a b => 1 + cost limit globals env a + cost limit globals env b
  NBoxCase _ a b c => 1 + cost limit globals env a + cost limit globals env b + cost limit globals env c
  NPatternLambda _ names body => 4 + 2 * inferredFieldNodes + cost limit globals (reverse (map spelling names) ++ env) body
  NConstructorCase _ _ constructor value branch motive =>
    8 + 3 * inferredParameterNodes + 3 * cost limit globals env constructor + cost limit globals env value + 2 * cost limit globals env branch +
      (case motive of Nothing => inferredResultNodes; Just explicit => cost limit globals env explicit)
  NInferCase _ _ value branch => 8 + cost limit globals env value + 2 * cost limit globals env branch + inferredResultNodes
  NPairCase _ motive value branch => 1 + cost limit globals env motive + cost limit globals env value + cost limit globals env branch
  NConstraintPi _ _ name a b => 1 + cost limit globals env a + cost limit globals (name :: env) b
  NDictionaryApply _ _ function argument => 2 + cost limit globals env function + (case argument of Nothing => 1; Just value => cost limit globals env value)
  NPi _ _ name a b => 1 + cost limit globals env a + cost limit globals (name :: env) b
  NLambda _ _ name a b => 1 + cost limit globals env a + cost limit globals (name :: env) b
  NApply _ a b => 1 + cost limit globals env a + cost limit globals env b
  NAscribe _ a b => 3 + cost limit globals env a + cost limit globals env b
  NLet _ _ name a value body => 2 + cost limit globals env a + cost limit globals env value +
                               cost limit globals (name :: env) body
  NSequence _ a b => 7 + cost limit globals env a + cost limit globals env b
  NDoBind _ name a action body => 3 + 2 * cost limit globals env a + cost limit globals env action +
                                  cost limit globals (name :: env) body
  NDoResult _ result body =>
    let resultSize = cost limit globals env result
     in 4 + resultSize + resultSize * cost limit globals env body

record Interface where
  constructor Exports
  name : List String
  bindings : List Weighted
  schemas : List InterfaceSchema

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
  ty <- resolve snapshot globals decl.expected
  value <- resolve snapshot globals decl.value
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
  if decl.dictionary then case weakHead typeReductionFuel ty of
    HeadForm (BoxType _ _) => Right ()
    HeadForm (Sigma _ _ _ _) => Right ()
    HeadForm _ => Left ({ stage := "runtime-checking" } (problem snapshot (Just decl.nameSpan.start)
      "Implementation signature must be a dictionary-shaped unary or dependent-pair type"))
    HeadLimit _ => Left ({ stage := "runtime-checking" } (problem snapshot (Just decl.nameSpan.start)
      "Implementation dictionary type reduction budget exhausted"))
    else Right ()
  let local = weighted (GlobalWithQuantity decl.quantity decl.name ty value)
  let qualified = Weight (GlobalWithQuantity decl.quantity (moduleText name ++ "." ++ decl.name) ty value) local.size
  following <- compileDeclarations snapshot name (local :: qualified :: globals) rest (minus remaining estimate)
  Right (Definitions (local :: following.locals)
           (if decl.exported then qualified :: following.exports else following.exports) following.remaining)

directImports : ModuleSnapshot -> List Interface -> Either GraphError (List Weighted)
directImports snapshot interfaces = collect snapshot.document.imports
  where
    collect : List ImportDeclaration -> Either GraphError (List Weighted)
    collect [] = Right []
    collect (dependency :: rest) = case find (\entry => entry.name == dependency.components) interfaces of
      Nothing => Left (problem snapshot (Just dependency.span.start) "Missing checked dependency interface")
      Just entry => (entry.bindings ++) <$> collect rest

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

compileGraph : ModuleGraph -> List Weighted -> List Interface -> Nat -> List ModuleSnapshot ->
               Either GraphError CheckedProject
compileGraph graph prelude interfaces remaining [] =
  Left (GraphFailure graph.entry "" Nothing "No entry snapshot in graph")
compileGraph graph prelude interfaces remaining (snapshot :: rest) = do
  if snapshot.path == graph.entry && not (null rest)
     then Left (problem snapshot Nothing "Entry snapshot must be last in dependency order")
     else Right ()
  imported <- directImports snapshot interfaces
  let schemas = directSchemas snapshot interfaces
  let globals = imported ++ prelude
  case snapshot.document.moduleHeader of
    Nothing => if snapshot.path /= graph.entry then Left (problem snapshot Nothing "Anonymous dependency") else do
      term <- anonymous snapshot schemas globals remaining
      case inferRuntime checkingDepth typeReductionFuel Empty term of
        Left err => Left ({ stage := "runtime-checking" } (problem snapshot Nothing ("Entry checking: " ++ show err)))
        Right checked => Right (Project graph term checked.inferredType)
    Just header => do
      if any (\entry => entry.name == header.components) interfaces
         then Left (problem snapshot (Just header.nameSpan.start) "Duplicate checked module identity")
         else Right ()
      declarations <- case snapshot.document.body of
        DeclarationDocument authored => elaborateAt snapshot schemas authored
        EmptyDocument => Right []
        _ => Left (problem snapshot Nothing "Named modules require declarations")
      compiled <- compileDeclarations snapshot header.components globals declarations remaining
      if snapshot.path == graph.entry
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
              Right checked => Right (Project graph term checked.inferredType)
         else let visible = case snapshot.document.body of
                    DeclarationDocument authored => exportedSchemas (moduleText header.components) authored
                    _ => []
               in compileGraph graph prelude (Exports header.components compiled.exports visible :: interfaces)
                           compiled.remaining rest

||| Check every dependency declaration before exposing its qualified exports.
||| Expansion budget concerns elaboration, not normalization/allocation/time bounds.
public export
checkModuleGraph : ModuleGraph -> Either GraphError CheckedProject
checkModuleGraph graph = do
  prelude <- case preludeGlobals of
    Left err => Left ({ stage := "prelude" } (GraphFailure graph.entry "" Nothing ("Bundled prelude: " ++ err)))
    Right globals => Right (map weighted globals)
  compileGraph graph prelude [] 200000 graph.modules

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

public export
projectReport : CheckedProject -> List String
projectReport project =
  ["Module checking: accepted (closed transparent globals)",
   "Modules: " ++ show (length project.graph.modules),
   "Type: " ++ renderType project.inferredType]
