-- Checked closed module interfaces, not opaque globals or project editor reports.
module Fibril.Driver.ModuleCheck

import Data.List
import Data.List1
import Data.Maybe
import Data.String
import Data.SortedSet
import Data.SortedMap
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
import Fibril.Elaboration.Expression.Conversion
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
    NRecType _ _ => 1
    NRecEnd _ ty => 1 + cost limit globals env ty
    NRecMore _ ty tail => 1 + cost limit globals env ty + cost limit globals env tail
    NRecFold _ motive base next value => 1 + cost limit globals env motive + cost limit globals env base + cost limit globals env next + cost limit globals env value
    NSeqType _ _ element => 1 + cost limit globals env element
    NSeqNil _ ty => 1 + cost limit globals env ty
    NSeqCons _ ty head tail => 1 + cost limit globals env ty + cost limit globals env head + cost limit globals env tail
    NSeqFold _ motive base next value => 1 + cost limit globals env motive + cost limit globals env base + cost limit globals env next + cost limit globals env value
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
  -- Two payload binders may each require an admitted type annotation.
  -- Re-traversing nested case bodies per copy would make admission exponential.
  dataArmsCost : Nat -> List Weighted -> List String -> Nat -> List (Token, List Token, Expr) -> Nat
  dataArmsCost limit globals env copies [] = 0
  dataArmsCost limit globals env copies ((_, binder, body) :: rest) =
    let branch = cost limit globals (reverse (map spelling binder) ++ env) body
        binary = length binder > 1
        reserve : Nat = if binary then 2051 else 1025
        annotation : Nat = if binary then 1026 else 513 in
      min (S limit) (reserve + copies * (annotation + branch) + dataArmsCost limit globals env copies rest)

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

||| Authored source spans recorded only for a successfully checked lowering.
public export
record RecursiveSite where
  constructor StructuralSite
  path : String
  origin : SourceSpan
  target : SourceSpan

record Compiled where
  constructor Definitions
  locals : List Weighted
  exports : List Weighted
  sites : List RecursiveSite
  remaining : Nat

public export
record CheckedProject where
  constructor Project
  graph : ModuleGraph
  term : Term 0
  inferredType : Term 0
  recursiveSites : List RecursiveSite
  ||| Checked visible export spelling and canonical origin for dependency modules.
  checkedExports : List (List String, List (String, String))

exportIndex : List Interface -> List (List String, List (String, String))
exportIndex interfaces = map (\entry => (entry.name, mapMaybe exportedName entry.bindings)) interfaces
  where
    exportedName : Weighted -> Maybe (String, String)
    exportedName binding = map (\origin => (binding.global.name, origin)) binding.global.canonicalName

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

-- Internal-only: '$' cannot begin an authored identifier. The original syntax
-- remains the source of navigation; this name is never emitted as a source use.
private
recursiveResultName : String
recursiveResultName = "$nat.recursive.result"

-- Admit only binder-free ordinary expressions. Every occurrence of the three
-- relevant source names is inspected; direct self-calls on mutually exclusive
-- paths can share the linear induction-result slot. The core checker verifies
-- that every runtime path uses that slot exactly once.
private
recursiveExpression : String -> String -> String -> Expr -> Maybe (Bool, Expr)
recursiveExpression name argument predecessor (NApply span (NRef site function) (NRef valueSite value)) =
  if function == name && value == predecessor
    then Just (True, NRef site recursiveResultName)
    else do
      (leftUsed, left) <- recursiveExpression name argument predecessor (NRef site function)
      (rightUsed, right) <- recursiveExpression name argument predecessor (NRef valueSite value)
      if leftUsed && rightUsed then Nothing else Just (leftUsed || rightUsed, NApply span left right)
recursiveExpression name argument predecessor (NApply span function value) = do
  (leftUsed, left) <- recursiveExpression name argument predecessor function
  (rightUsed, right) <- recursiveExpression name argument predecessor value
  if leftUsed && rightUsed then Nothing else Just (leftUsed || rightUsed, NApply span left right)
recursiveExpression name argument predecessor (NIf span condition yes no) = do
  (conditionUsed, condition) <- recursiveExpression name argument predecessor condition
  (yesUsed, yes) <- recursiveExpression name argument predecessor yes
  (noUsed, no) <- recursiveExpression name argument predecessor no
  if conditionUsed && (yesUsed || noUsed)
    then Nothing else Just (conditionUsed || yesUsed || noUsed, NIf span condition yes no)
recursiveExpression name argument predecessor expr@(NRef _ ref) =
  if ref == name || ref == argument || ref == predecessor || ref == recursiveResultName
    then Nothing else Just (False, expr)
recursiveExpression name argument predecessor expr@(NQualifiedRef _ ref) =
  case reverse (forget (Data.String.split (== '.') ref)) of
    short :: _ => if short == name then Nothing else Just (False, expr)
    [] => Nothing
recursiveExpression _ _ _ expr@(NSort _ _) = Just (False, expr)
recursiveExpression _ _ _ expr@(NUnitType _) = Just (False, expr)
recursiveExpression _ _ _ expr@(NUnitValue _) = Just (False, expr)
recursiveExpression _ _ _ expr@(NStringType _) = Just (False, expr)
recursiveExpression _ _ _ expr@(NStringValue _ _) = Just (False, expr)
recursiveExpression _ _ _ expr@(NBoolType _) = Just (False, expr)
recursiveExpression _ _ _ expr@(NBoolValue _ _) = Just (False, expr)
recursiveExpression _ _ _ _ = Nothing

-- One erased family parameter is held fixed throughout structural recursion.
-- Only the authored parameter, or its safe omitted implicit form, is accepted.
private
polyRecursiveExpression : Bool -> String -> String -> String -> String -> Expr -> Maybe (Bool, Expr)
polyRecursiveExpression inferred param name argument tail (NApply span (NRef site function) (NRef valueSite value)) =
  if inferred && function == name && value == tail then Just (True, NRef site recursiveResultName) else do
    (leftUsed, left) <- polyRecursiveExpression inferred param name argument tail (NRef site function)
    (rightUsed, right) <- polyRecursiveExpression inferred param name argument tail (NRef valueSite value)
    if leftUsed && rightUsed then Nothing else Just (leftUsed || rightUsed, NApply span left right)
polyRecursiveExpression inferred param name argument tail (NApply span left@(NApply _ (NRef site function) (NRef _ supplied)) right@(NRef _ value)) =
  if not inferred && function == name && supplied == param && value == tail
    then Just (True, NRef site recursiveResultName)
    else do
      (leftUsed, left) <- polyRecursiveExpression inferred param name argument tail left
      (rightUsed, right) <- polyRecursiveExpression inferred param name argument tail right
      if leftUsed && rightUsed then Nothing else Just (leftUsed || rightUsed, NApply span left right)
polyRecursiveExpression inferred param name argument tail (NApply span left@(NImplicitApply _ (NRef site function) (NRef _ supplied)) right@(NRef _ value)) =
  if inferred && function == name && supplied == param && value == tail
    then Just (True, NRef site recursiveResultName)
    else do
      (leftUsed, left) <- polyRecursiveExpression inferred param name argument tail left
      (rightUsed, right) <- polyRecursiveExpression inferred param name argument tail right
      if leftUsed && rightUsed then Nothing else Just (leftUsed || rightUsed, NApply span left right)
polyRecursiveExpression inferred param name argument tail (NApply span function value) = do
  (leftUsed, left) <- polyRecursiveExpression inferred param name argument tail function
  (rightUsed, right) <- polyRecursiveExpression inferred param name argument tail value
  if leftUsed && rightUsed then Nothing else Just (leftUsed || rightUsed, NApply span left right)
polyRecursiveExpression inferred param name argument tail (NImplicitApply span function value) = do
  (leftUsed, left) <- polyRecursiveExpression inferred param name argument tail function
  (rightUsed, right) <- polyRecursiveExpression inferred param name argument tail value
  if leftUsed && rightUsed then Nothing else Just (leftUsed || rightUsed, NImplicitApply span left right)
polyRecursiveExpression inferred param name argument tail (NIf span condition yes no) = do
  (conditionUsed, condition) <- polyRecursiveExpression inferred param name argument tail condition
  (yesUsed, yes) <- polyRecursiveExpression inferred param name argument tail yes
  (noUsed, no) <- polyRecursiveExpression inferred param name argument tail no
  if conditionUsed && (yesUsed || noUsed)
    then Nothing else Just (conditionUsed || yesUsed || noUsed, NIf span condition yes no)
polyRecursiveExpression inferred param name argument tail expr@(NRef _ ref) =
  if ref == name || ref == argument || ref == tail || ref == recursiveResultName
    then Nothing else Just (False, expr)
polyRecursiveExpression inferred param name argument tail expr@(NQualifiedRef _ ref) =
  case reverse (forget (Data.String.split (== '.') ref)) of
    short :: _ => if short == name then Nothing else Just (False, expr)
    [] => Nothing
polyRecursiveExpression _ _ _ _ _ expr@(NSort _ _) = Just (False, expr)
polyRecursiveExpression _ _ _ _ _ expr@(NUnitType _) = Just (False, expr)
polyRecursiveExpression _ _ _ _ _ expr@(NUnitValue _) = Just (False, expr)
polyRecursiveExpression _ _ _ _ _ expr@(NStringType _) = Just (False, expr)
polyRecursiveExpression _ _ _ _ _ expr@(NStringValue _ _) = Just (False, expr)
polyRecursiveExpression _ _ _ _ _ expr@(NBoolType _) = Just (False, expr)
polyRecursiveExpression _ _ _ _ _ expr@(NBoolValue _ _) = Just (False, expr)
polyRecursiveExpression _ _ _ _ _ _ = Nothing

-- Prefix arguments must be passed explicitly, in authored visibility order,
-- with the same lexical binders. No omitted or computed argument is guessed.
private
prefixModes : Nat -> List Token -> List (Bool, String)
prefixModes _ [] = []
prefixModes Z (token :: rest) = (False, token.spelling) :: prefixModes Z rest
prefixModes (S count) (token :: rest) = (True, token.spelling) :: prefixModes count rest

private
peelUniformCall : String -> List (Bool, String) -> Expr -> Maybe SourceSpan
peelUniformCall name [] (NRef site function) = if function == name then Just site else Nothing
peelUniformCall name ((True, expected) :: rest) (NImplicitApply _ function (NRef _ supplied)) =
  if expected == supplied then peelUniformCall name rest function else Nothing
peelUniformCall name ((False, expected) :: rest) (NApply _ function (NRef _ supplied)) =
  if expected == supplied then peelUniformCall name rest function else Nothing
peelUniformCall _ _ _ = Nothing

private
uniformCallSite : String -> List (Bool, String) -> String -> Expr -> Maybe SourceSpan
uniformCallSite name reversed tail (NApply _ function (NRef _ value)) =
  if value == tail then peelUniformCall name reversed function else Nothing
uniformCallSite _ _ _ _ = Nothing

private
uniformExpression : String -> List (Bool, String) -> String -> String -> Expr -> Maybe (Bool, Expr)
uniformExpression name reversed argument tail expression = case uniformCallSite name reversed tail expression of
  Just site => Just (True, NRef site recursiveResultName)
  Nothing => case expression of
    NApply span function value => do
      (leftUsed, left) <- uniformExpression name reversed argument tail function
      (rightUsed, right) <- uniformExpression name reversed argument tail value
      if leftUsed && rightUsed then Nothing else Just (leftUsed || rightUsed, NApply span left right)
    NImplicitApply span function value => do
      (leftUsed, left) <- uniformExpression name reversed argument tail function
      (rightUsed, right) <- uniformExpression name reversed argument tail value
      if leftUsed && rightUsed then Nothing else Just (leftUsed || rightUsed, NImplicitApply span left right)
    NIf span condition yes no => do
      (conditionUsed, condition) <- uniformExpression name reversed argument tail condition
      (yesUsed, yes) <- uniformExpression name reversed argument tail yes
      (noUsed, no) <- uniformExpression name reversed argument tail no
      if conditionUsed && (yesUsed || noUsed)
        then Nothing else Just (conditionUsed || yesUsed || noUsed, NIf span condition yes no)
    NRef _ ref => if ref == name || ref == argument || ref == tail || ref == recursiveResultName then Nothing else Just (False, expression)
    NQualifiedRef _ ref => case reverse (forget (Data.String.split (== '.') ref)) of
      short :: _ => if short == name then Nothing else Just (False, expression)
      [] => Nothing
    NSort _ _ => Just (False, expression)
    NUnitType _ => Just (False, expression)
    NUnitValue _ => Just (False, expression)
    NStringType _ => Just (False, expression)
    NStringValue _ _ => Just (False, expression)
    NBoolType _ => Just (False, expression)
    NBoolValue _ _ => Just (False, expression)
    _ => Nothing

-- Only a fixed-size source-call plan is inspected before module admission;
-- this walk does not construct rewritten expressions or cloned core terms.
private
uniformCallPresent : String -> List (Bool, String) -> String -> Expr -> Bool
uniformCallPresent name reversed tail expression = case uniformCallSite name reversed tail expression of
  Just _ => True
  Nothing => case expression of
    NApply _ left right => uniformCallPresent name reversed tail left || uniformCallPresent name reversed tail right
    NImplicitApply _ left right => uniformCallPresent name reversed tail left || uniformCallPresent name reversed tail right
    NIf _ condition yes no => uniformCallPresent name reversed tail condition || uniformCallPresent name reversed tail yes || uniformCallPresent name reversed tail no
    _ => False

private
natBuiltinsVisible : List Weighted -> Bool
natBuiltinsVisible globals =
  -- Imported/local entries always also have a qualified identity. Refuse the
  -- special syntax if either name could have been shadowed, even by an alias
  -- whose value happens to equal the primitive.
  if not (null (qualifiedCandidates "Zero" (map global globals))) ||
     not (null (qualifiedCandidates "Succ" (map global globals))) then False else
    case (find (\entry => entry.global.name == "Zero") globals,
          find (\entry => entry.global.name == "Succ") globals) of
      (Just zero, Just succ) => zero.global.quantity == Unrestricted && succ.global.quantity == Unrestricted &&
        sameSyntax zero.global.value NatZero &&
        sameSyntax succ.global.value (Lambda Linear NatType (NatSucc (Variable FZ)))
      _ => False

private
natRecursiveEquation : List Weighted -> String -> Term 0 -> Expr -> Either ResolveError (Maybe (Term 0))
natRecursiveEquation globals name ty (NEquationLambda _ [argument] _
  (NDataCase span (NRef _ scrutinee) Nothing [(first, firstBinder, firstBody), (second, secondBinder, secondBody)])) = do
  if name == "Zero" || name == "Succ" || argument.spelling == "_" || argument.spelling == name ||
     argument.spelling == "Zero" || argument.spelling == "Succ" ||
     scrutinee /= argument.spelling || not (natBuiltinsVisible globals) ||
     isJust (find (\entry => entry.global.name == name) globals) ||
     not (null (qualifiedCandidates name (map global globals))) then Right Nothing else do
  -- Never reduce an unchecked signature without the guarded node/payload
  -- admission used by speculative conversion. Exhaustion is inconclusive.
  case guardedNormal typeReductionFuel ty of
    Just (Pi Linear NatType result) => case dropNewest result of
      Nothing => Left (CannotElaborate span.start "Structural Nat equations require a result independent of the argument")
      Just resultType => do
        (base, predecessor, body) <- case (first.spelling, firstBinder, second.spelling, secondBinder) of
          ("Zero", [], "Succ", [predecessor]) => Right (firstBody, predecessor, secondBody)
          ("Succ", [predecessor], "Zero", []) => Right (secondBody, predecessor, firstBody)
          _ => Left (CannotElaborate span.start "Structural Nat equations require one Zero arm and one Succ predecessor arm")
        if predecessor.spelling == "_" || predecessor.spelling == name || predecessor.spelling == argument.spelling ||
           predecessor.spelling == "Zero" || predecessor.spelling == "Succ"
          then Left (CannotElaborate predecessor.span.start "Invalid structural predecessor binder") else Right ()
        baseExpr <- case recursiveExpression name argument.spelling predecessor.spelling base of
          Just (False, value) => Right value
          _ => Left (CannotElaborate (extent base).start "Structural zero arm cannot use the function, input, predecessor or unsupported syntax")
        stepExpr <- case recursiveExpression name argument.spelling predecessor.spelling body of
          Just (True, value) => Right value
          _ => Left (CannotElaborate (extent body).start "Structural successor arm needs direct calls on the predecessor along exclusive paths and supported binder-free syntax")
        let checkedGlobals = map global globals
        zero <- elaborateExpected checkedGlobals Empty [] resultType baseExpr
        let stepContext = Extend (Extend Empty Erased NatType) Linear (weaken resultType)
        successor <- elaborateExpected checkedGlobals stepContext [recursiveResultName, "$nat.predecessor"]
                        (weaken (weaken resultType)) stepExpr
        let motive : Term 1 = Lambda Erased NatType (weaken (weaken resultType))
        let branch : Term 1 = weaken (Lambda Erased NatType (Lambda Linear (weaken resultType) successor))
        Right (Just (Lambda Linear NatType (NatRec motive (weaken zero) branch (Variable FZ))))
    _ => Right Nothing
natRecursiveEquation _ _ _ _ = Right Nothing

-- Constructor spelling and schema metadata are not evidence: use only visible
-- unrestricted checked globals whose normalized values match this exact family.
private
recursiveConstructorTag : List Weighted -> String -> String -> Maybe Nat
recursiveConstructorTag globals key name = do
  entry <- find (\item => item.global.name == name) globals
  if entry.global.quantity /= Unrestricted then Nothing else do
    value <- guardedNormal typeReductionFuel entry.global.value
    if sameSyntax value (RecEnd (RecType key)) then Just 0 else
      if sameSyntax value (Lambda Linear (RecType key) (RecMore (RecType key) (Variable FZ)))
        then Just 1 else Nothing

-- This read-only probe allocates no rewritten expression before admission.
private
structuralCallPresent : String -> String -> Expr -> Bool
structuralCallPresent name predecessor (NApply _ (NRef _ function) (NRef _ value)) =
  function == name && value == predecessor
structuralCallPresent name predecessor (NApply _ function value) =
  structuralCallPresent name predecessor function || structuralCallPresent name predecessor value
structuralCallPresent name predecessor (NIf _ condition yes no) =
  structuralCallPresent name predecessor condition || structuralCallPresent name predecessor yes || structuralCallPresent name predecessor no
structuralCallPresent _ _ _ = False

private
polymorphicCallPresent : String -> String -> Expr -> Bool
polymorphicCallPresent name tail (NApply _ (NRef _ function) (NRef _ value)) = function == name && value == tail
polymorphicCallPresent name tail (NApply _ left@(NApply _ (NRef _ function) _) right@(NRef _ value)) =
  (function == name && value == tail) || polymorphicCallPresent name tail left || polymorphicCallPresent name tail right
polymorphicCallPresent name tail (NApply _ left@(NImplicitApply _ (NRef _ function) _) right@(NRef _ value)) =
  (function == name && value == tail) || polymorphicCallPresent name tail left || polymorphicCallPresent name tail right
polymorphicCallPresent name tail (NApply _ function value) =
  polymorphicCallPresent name tail function || polymorphicCallPresent name tail value
polymorphicCallPresent name tail (NImplicitApply _ function value) =
  polymorphicCallPresent name tail function || polymorphicCallPresent name tail value
polymorphicCallPresent name tail (NIf _ condition yes no) =
  polymorphicCallPresent name tail condition || polymorphicCallPresent name tail yes || polymorphicCallPresent name tail no
polymorphicCallPresent _ _ _ = False


private
unaryRecursiveEquation : List Weighted -> String -> Term 0 -> Expr -> Either ResolveError (Maybe (Term 0))
unaryRecursiveEquation globals name ty (NEquationLambda _ [argument] _
  (NDataCase span (NRef _ scrutinee) Nothing [(first, firstBinder, firstBody), (second, secondBinder, secondBody)])) = do
  if argument.spelling == "_" || argument.spelling == name || scrutinee /= argument.spelling ||
     isJust (find (\entry => entry.global.name == name) globals) ||
     not (null (qualifiedCandidates name (map global globals))) then Right Nothing else do
  case guardedNormal typeReductionFuel ty of
    Just (Pi Linear family@(RecType key) result) =>
      case (recursiveConstructorTag globals key first.spelling, firstBinder,
            recursiveConstructorTag globals key second.spelling, secondBinder) of
        (Just 0, [], Just 1, [predecessor]) => lower family result firstBody predecessor secondBody
        (Just 1, [predecessor], Just 0, []) => lower family result secondBody predecessor firstBody
        _ => Right Nothing
    _ => Right Nothing
  where
    lower : Term 0 -> Term 1 -> Expr -> Token -> Expr -> Either ResolveError (Maybe (Term 0))
    lower family result base predecessor body = do
      if predecessor.spelling == "_" || predecessor.spelling == name || predecessor.spelling == argument.spelling ||
         predecessor.spelling == first.spelling || predecessor.spelling == second.spelling ||
         argument.spelling == first.spelling || argument.spelling == second.spelling ||
         name == first.spelling || name == second.spelling ||
         not (structuralCallPresent name predecessor.spelling body)
        then Right Nothing else do
      case (recursiveExpression name argument.spelling predecessor.spelling base,
            recursiveExpression name argument.spelling predecessor.spelling body) of
        (Just (False, baseExpr), Just (True, stepExpr)) => do
          resultType <- case dropNewest result of
            Nothing => Left (CannotElaborate span.start "Structural recursive equations require a result independent of the argument")
            Just resultType => Right resultType
          let checkedGlobals = map global globals
          baseTerm <- elaborateExpected checkedGlobals Empty [] resultType baseExpr
          let stepContext = Extend (Extend Empty Erased family) Linear (weaken resultType)
          stepTerm <- elaborateExpected checkedGlobals stepContext [recursiveResultName, "$rec.predecessor"]
                        (weaken (weaken resultType)) stepExpr
          let motive : Term 1 = Lambda Erased (weaken family) (weaken (weaken resultType))
          let branch : Term 1 = weaken (Lambda Erased family (Lambda Linear (weaken resultType) stepTerm))
          Right (Just (Lambda Linear family (RecFold motive (weaken baseTerm) branch (Variable FZ))))
        _ => Right Nothing
unaryRecursiveEquation _ _ _ _ = Right Nothing

-- Share the exact guarded comparison used for direct sequence cases.
private
sequenceConstructorTag : List Weighted -> Context n -> Term n -> Term n -> Token -> Maybe Nat
sequenceConstructorTag globals context family element name = do
  entry <- find (\item => item.global.name == name.spelling) globals
  case checkedSequenceConstructor name.span.start context family element entry.global of
    Right tag => Just tag
    Left _ => Nothing

private
sequenceRecursiveEquation : List Weighted -> String -> Term 0 -> Expr -> Either ResolveError (Maybe (Term 0))
sequenceRecursiveEquation globals name ty (NEquationLambda _ [argument] _
  (NDataCase span (NRef _ scrutinee) Nothing [(first, firstBinder, firstBody), (second, secondBinder, secondBody)])) = do
  if argument.spelling == "_" || argument.spelling == name || scrutinee /= argument.spelling ||
     isJust (find (\entry => entry.global.name == name) globals) ||
     not (null (qualifiedCandidates name (map global globals))) then Right Nothing else do
  case guardedNormal typeReductionFuel ty of
    Just (Pi Linear family@(SeqType _ element) result) =>
      case (sequenceConstructorTag globals Empty family element first, firstBinder,
            sequenceConstructorTag globals Empty family element second, secondBinder) of
        (Just 0, [], Just 1, [head, tail]) => lower family element result firstBody head tail secondBody
        (Just 1, [head, tail], Just 0, []) => lower family element result secondBody head tail firstBody
        _ => Right Nothing
    _ => Right Nothing
  where
    lower : Term 0 -> Term 0 -> Term 1 -> Expr -> Token -> Token -> Expr -> Either ResolveError (Maybe (Term 0))
    lower family element result base head tail body = do
      if head.spelling == "_" || tail.spelling == "_" || head.spelling == tail.spelling ||
         head.spelling == name || head.spelling == argument.spelling ||
         head.spelling == first.spelling || head.spelling == second.spelling ||
         tail.spelling == name || tail.spelling == argument.spelling ||
         tail.spelling == first.spelling || tail.spelling == second.spelling ||
         argument.spelling == first.spelling || argument.spelling == second.spelling ||
         name == first.spelling || name == second.spelling ||
         not (structuralCallPresent name tail.spelling body)
        then Right Nothing else do
      case (recursiveExpression name argument.spelling tail.spelling base,
            recursiveExpression name argument.spelling tail.spelling body) of
        (Just (False, baseExpr), Just (True, stepExpr)) => do
          resultType <- case dropNewest result of
            Nothing => Left (CannotElaborate span.start "Structural sequence equations require a result independent of the argument")
            Just resultType => Right resultType
          let checkedGlobals = map global globals
          baseTerm <- elaborateExpected checkedGlobals Empty [] resultType baseExpr
          let stepContext = Extend (Extend (Extend Empty Linear element) Erased (weaken family)) Linear (weaken (weaken resultType))
          stepTerm <- elaborateExpected checkedGlobals stepContext [recursiveResultName, "$seq.tail", head.spelling]
                        (weaken (weaken (weaken resultType))) stepExpr
          let motive : Term 1 = Lambda Erased (weaken family) (weaken (weaken resultType))
          let step : Term 0 = Lambda Linear element (Lambda Erased (weaken family)
                                (Lambda Linear (weaken (weaken resultType)) stepTerm))
          Right (Just (Lambda Linear family (SeqFold motive (weaken baseTerm) (weaken step) (Variable FZ))))
        _ => Right Nothing
sequenceRecursiveEquation _ _ _ _ = Right Nothing

private
polymorphicSequenceEquation : List Weighted -> String -> Bool -> Term 0 -> Expr -> Either ResolveError (Maybe (Term 0))
polymorphicSequenceEquation globals name inferred ty (NEquationLambda _ [param, argument] _
  (NDataCase span (NRef _ scrutinee) Nothing [(first, firstBinder, firstBody), (second, secondBinder, secondBody)])) = do
  if param.spelling == "_" || argument.spelling == "_" ||
     param.spelling == name || argument.spelling == name || param.spelling == argument.spelling ||
     scrutinee /= argument.spelling || isJust (find (\entry => entry.global.name == name) globals) ||
     not (null (qualifiedCandidates name (map global globals))) then Right Nothing else do
  case guardedNormal typeReductionFuel ty of
    Just (Pi Erased (Universe 0) (Pi Linear family@(SeqType _ (Variable FZ)) result)) =>
      let context = Extend Empty Erased (Universe 0)
          element = Variable FZ in
      case (sequenceConstructorTag globals context family element first, firstBinder,
            sequenceConstructorTag globals context family element second, secondBinder) of
        (Just 0, [], Just 1, [head, tail]) => lower context family element result firstBody head tail secondBody
        (Just 1, [head, tail], Just 0, []) => lower context family element result secondBody head tail firstBody
        _ => Right Nothing
    _ => Right Nothing
  where
    lower : Context 1 -> Term 1 -> Term 1 -> Term 2 -> Expr -> Token -> Token -> Expr -> Either ResolveError (Maybe (Term 0))
    lower context family element result base head tail body = do
      if head.spelling == "_" || tail.spelling == "_" || head.spelling == tail.spelling ||
         head.spelling == name || head.spelling == param.spelling || head.spelling == argument.spelling ||
         head.spelling == first.spelling || head.spelling == second.spelling ||
         tail.spelling == name || tail.spelling == param.spelling || tail.spelling == argument.spelling ||
         tail.spelling == first.spelling || tail.spelling == second.spelling ||
         param.spelling == first.spelling || param.spelling == second.spelling ||
         argument.spelling == first.spelling || argument.spelling == second.spelling ||
         name == first.spelling || name == second.spelling ||
         not (polymorphicCallPresent name tail.spelling body)
        then Right Nothing else do
      case (polyRecursiveExpression inferred param.spelling name argument.spelling tail.spelling base,
            polyRecursiveExpression inferred param.spelling name argument.spelling tail.spelling body) of
        (Just (False, baseExpr), Just (True, stepExpr)) => do
          resultType <- case dropNewest result of
            Nothing => Left (CannotElaborate span.start "Structural sequence equations require a result independent of the argument")
            Just resultType => Right resultType
          let checkedGlobals = map global globals
          baseTerm <- elaborateExpected checkedGlobals context [param.spelling] resultType baseExpr
          let stepContext = Extend (Extend (Extend context Linear element) Erased (weaken family)) Linear (weaken (weaken resultType))
          stepTerm <- elaborateExpected checkedGlobals stepContext [recursiveResultName, "$seq.tail", head.spelling, param.spelling]
                        (weaken (weaken (weaken resultType))) stepExpr
          let motive : Term 2 = Lambda Erased (weaken family) (weaken (weaken resultType))
          let step : Term 1 = Lambda Linear element (Lambda Erased (weaken family)
                                (Lambda Linear (weaken (weaken resultType)) stepTerm))
          let body : Term 1 = Lambda Linear family (SeqFold motive (weaken baseTerm) (weaken step) (Variable FZ))
          Right (Just (Lambda Erased (Universe 0) body))
        _ => Right Nothing
polymorphicSequenceEquation _ _ _ _ _ = Right Nothing

-- A deliberately bounded accumulator form. It elaborates the authored update
-- into an ordinary function-valued fold; no termination graph is trusted.
private
accumulatorCall : String -> String -> Expr -> Maybe Expr
accumulatorCall name tail (NApply _ (NApply _ (NRef _ function) (NRef _ suppliedTail)) update) =
  if function == name && suppliedTail == tail then Just update else Nothing
accumulatorCall _ _ _ = Nothing

-- Do not let a removed input/tail/self binder resolve to a same-named global.
-- Binder-containing or otherwise unsupported source forms fail closed.
private
accumulatorUpdateSafe : List String -> Expr -> Bool
accumulatorUpdateSafe forbidden (NRef _ ref) = not (elem ref forbidden)
accumulatorUpdateSafe forbidden (NQualifiedRef _ ref) = case reverse (forget (Data.String.split (== '.') ref)) of
  short :: _ => not (elem short forbidden)
  [] => False
accumulatorUpdateSafe forbidden (NApply _ function argument) =
  accumulatorUpdateSafe forbidden function && accumulatorUpdateSafe forbidden argument
accumulatorUpdateSafe forbidden (NImplicitApply _ function argument) =
  accumulatorUpdateSafe forbidden function && accumulatorUpdateSafe forbidden argument
accumulatorUpdateSafe forbidden (NIf _ condition yes no) =
  accumulatorUpdateSafe forbidden condition && accumulatorUpdateSafe forbidden yes && accumulatorUpdateSafe forbidden no
accumulatorUpdateSafe _ (NSort _ _) = True
accumulatorUpdateSafe _ (NUnitType _) = True
accumulatorUpdateSafe _ (NUnitValue _) = True
accumulatorUpdateSafe _ (NStringType _) = True
accumulatorUpdateSafe _ (NStringValue _ _) = True
accumulatorUpdateSafe _ (NBoolType _) = True
accumulatorUpdateSafe _ (NBoolValue _ _) = True
accumulatorUpdateSafe _ _ = False

-- The two original update locals are [accumulator, head]. In the generated
-- step they are [accumulator, induction result, erased tail, head].
private
accumulatorScope : Fin 2 -> Fin 4
accumulatorScope FZ = FZ
accumulatorScope (FS FZ) = FS (FS (FS FZ))

private
accumulatorSequenceEquation : List Weighted -> String -> Term 0 -> Expr -> Either ResolveError (Maybe (Term 0))
accumulatorSequenceEquation globals name ty (NEquationLambda _ [argument, accumulator] _
  (NDataCase _ (NRef _ scrutinee) Nothing [(first, firstBinder, firstBody), (second, secondBinder, secondBody)])) = do
  let initial : List String = [name, argument.spelling, accumulator.spelling]
  if any (== "_") initial || length (nub initial) /= length initial || scrutinee /= argument.spelling ||
     isJust (find (\entry => entry.global.name == name) globals) ||
     not (null (qualifiedCandidates name (map global globals))) then Right Nothing else
    case guardedNormal typeReductionFuel ty of
      Just (Pi Linear family@(SeqType _ element) (Pi Linear accumulatorType result)) =>
        case (dropNewest accumulatorType, dropNewest result >>= dropNewest) of
          (Just accType, Just resultType) =>
            if not (sameSyntax accType resultType) then Right Nothing else
              case (sequenceConstructorTag globals Empty family element first, firstBinder,
                    sequenceConstructorTag globals Empty family element second, secondBinder) of
                (Just 0, [], Just 1, [head, tail]) => lower family element accType firstBody head tail secondBody
                (Just 1, [head, tail], Just 0, []) => lower family element accType secondBody head tail firstBody
                _ => Right Nothing
          _ => Right Nothing
      _ => Right Nothing
  where
    lower : Term 0 -> Term 0 -> Term 0 -> Expr -> Token -> Token -> Expr -> Either ResolveError (Maybe (Term 0))
    lower family element accType base head tail body = do
      let names : List String = [name, argument.spelling, accumulator.spelling, head.spelling, tail.spelling]
      if any (== "_") names || length (nub names) /= length names ||
         any (\entry => entry == first.spelling || entry == second.spelling) names
        then Right Nothing else do
      case (base, accumulatorCall name tail.spelling body) of
        (NRef _ baseName, Just update) =>
          if baseName /= accumulator.spelling ||
             not (accumulatorUpdateSafe [name, argument.spelling, tail.spelling, recursiveResultName] update)
            then Right Nothing else do
              -- Elaborate the exact authored update, including implicit
              -- metadata, then check its linear uses independently.
              let updateContext = Extend (Extend Empty Linear element) Linear (weaken accType)
              updateTerm <- elaborateExpected (map global globals) updateContext [accumulator.spelling, head.spelling]
                              (weaken (weaken accType)) update
              case checkRuntime checkingDepth typeReductionFuel updateContext updateTerm (weaken (weaken accType)) of
                Left (TypingError CheckingLimit) => Left (CannotElaborate (extent update).start "Accumulator update checking budget exhausted")
                Left (TypingError ReductionLimit) => Left (CannotElaborate (extent update).start "Accumulator update reduction budget exhausted")
                Left _ => Right Nothing
                Right _ => do
                  let continuation : Term 0 = Pi Linear accType (weaken accType)
                  let baseTerm : Term 0 = Lambda Linear accType (Variable FZ)
                  let stepTerm : Term 0 = Lambda Linear element (Lambda Erased (weaken family)
                        (Lambda Linear (weaken (weaken continuation))
                          (Lambda Linear (weaken (weaken (weaken accType)))
                            (Apply (Variable (FS FZ)) (rename accumulatorScope updateTerm)))))
                  let motive : Term 1 = Lambda Erased (weaken family) (weaken (weaken continuation))
                  Right (Just (Lambda Linear family (SeqFold motive (weaken baseTerm) (weaken stepTerm) (Variable FZ))))
        _ => Right Nothing
accumulatorSequenceEquation _ _ _ _ = Right Nothing

-- Scope-indexed prefix peeling. Erased and unrestricted parameters are held
-- fixed across each recursive call; the final linear input is a checked
-- sequence, unary recursive value or Nat.
private
uniformStructuralCandidate : List Weighted -> String -> Nat -> Term 0 -> SourceSpan -> String ->
  Token -> List Token -> Expr -> Token -> List Token -> Expr -> Token -> List Token ->
  Either ResolveError (Maybe (Term 0))
uniformStructuralCandidate globals name implicitCount ty span scrutinee first firstBinder firstBody second secondBinder secondBody argument params =
  let reversed = reverse (prefixModes implicitCount params)
      candidate = case (firstBinder, secondBinder) of
        ([], [_, tail]) => uniformCallPresent name reversed tail.spelling secondBody
        ([_, tail], []) => uniformCallPresent name reversed tail.spelling firstBody
        ([], [tail]) => uniformCallPresent name reversed tail.spelling secondBody
        ([tail], []) => uniformCallPresent name reversed tail.spelling firstBody
        _ => False
      names : List String = name :: map spelling params ++ [argument.spelling] in
  if length params > 64 || implicitCount > length params || not candidate ||
     any (== "_") names || length (nub names) /= length names || scrutinee /= argument.spelling ||
     isJust (find (\entry => entry.global.name == name) globals) ||
     not (null (qualifiedCandidates name (map global globals)))
    then Right Nothing else
    case guardedNormal typeReductionFuel ty of
      Nothing => Right Nothing
      Just exposed => walk Empty [] params (prefixModes implicitCount params) exposed
  where
    lower : Context n -> Vect n String -> Term n -> Term n -> Term (S n) -> Expr -> Token -> Token -> Expr ->
            Either ResolveError (Maybe (Term n))
    lower context env family element result base head tail body = do
      let names : List String = name :: map spelling params ++ [argument.spelling, head.spelling, tail.spelling]
      let reversed = reverse (prefixModes implicitCount params)
      if any (== "_") names || length (nub names) /= length names ||
         any (\entry => entry == first.spelling || entry == second.spelling) names ||
         not (uniformCallPresent name reversed tail.spelling body)
        then Right Nothing else do
      case (uniformExpression name reversed argument.spelling tail.spelling base,
            uniformExpression name reversed argument.spelling tail.spelling body) of
        (Just (False, baseExpr), Just (True, stepExpr)) => do
          resultType <- case dropNewest result of
            Nothing => Left (CannotElaborate span.start "Structural sequence equations require a result independent of the input")
            Just resultType => Right resultType
          let checkedGlobals = map global globals
          baseTerm <- elaborateExpected checkedGlobals context env resultType baseExpr
          let stepContext = Extend (Extend (Extend context Linear element) Erased (weaken family)) Linear (weaken (weaken resultType))
          stepTerm <- elaborateExpected checkedGlobals stepContext (recursiveResultName :: "$seq.tail" :: head.spelling :: env)
                        (weaken (weaken (weaken resultType))) stepExpr
          let motive = Lambda Erased (weaken family) (weaken (weaken resultType))
          let step = Lambda Linear element (Lambda Erased (weaken family)
                       (Lambda Linear (weaken (weaken resultType)) stepTerm))
          Right (Just (Lambda Linear family (SeqFold motive (weaken baseTerm) (weaken step) (Variable FZ))))
        _ => Right Nothing


    lowerUnary : Bool -> Context n -> Vect n String -> Term n -> Term (S n) -> Expr -> Token -> Expr ->
                 Either ResolveError (Maybe (Term n))
    lowerUnary natural context env family result base predecessor body = do
      let names : List String = name :: map spelling params ++ [argument.spelling, predecessor.spelling]
      let reversed = reverse (prefixModes implicitCount params)
      if any (== "_") names || length (nub names) /= length names ||
         any (\entry => entry == first.spelling || entry == second.spelling) names ||
         not (uniformCallPresent name reversed predecessor.spelling body)
        then Right Nothing else do
      case (uniformExpression name reversed argument.spelling predecessor.spelling base,
            uniformExpression name reversed argument.spelling predecessor.spelling body) of
        (Just (False, baseExpr), Just (True, stepExpr)) => do
          resultType <- case dropNewest result of
            Nothing => Left (CannotElaborate span.start "Structural recursive equations require a result independent of the input")
            Just resultType => Right resultType
          let checkedGlobals = map global globals
          baseTerm <- elaborateExpected checkedGlobals context env resultType baseExpr
          let stepContext = Extend (Extend context Erased family) Linear (weaken resultType)
          stepTerm <- elaborateExpected checkedGlobals stepContext (recursiveResultName :: "$structural.predecessor" :: env)
                        (weaken (weaken resultType)) stepExpr
          let motive = Lambda Erased (weaken family) (weaken (weaken resultType))
          let step = Lambda Erased family (Lambda Linear (weaken resultType) stepTerm)
          let folded = if natural then NatRec motive (weaken baseTerm) (weaken step) (Variable FZ)
                                  else RecFold motive (weaken baseTerm) (weaken step) (Variable FZ)
          Right (Just (Lambda Linear family folded))
        _ => Right Nothing

    walk : Context n -> Vect n String -> List Token -> List (Bool, String) -> Term n -> Either ResolveError (Maybe (Term n))
    walk context env [] [] (Pi Linear NatType result) =
      if not (natBuiltinsVisible globals) then Right Nothing else
        case (first.spelling, firstBinder, second.spelling, secondBinder) of
          ("Zero", [], "Succ", [predecessor]) => lowerUnary True context env NatType result firstBody predecessor secondBody
          ("Succ", [predecessor], "Zero", []) => lowerUnary True context env NatType result secondBody predecessor firstBody
          _ => Right Nothing
    walk context env [] [] (Pi Linear family@(RecType key) result) =
      case (recursiveConstructorTag globals key first.spelling, firstBinder,
            recursiveConstructorTag globals key second.spelling, secondBinder) of
        (Just 0, [], Just 1, [predecessor]) => lowerUnary False context env family result firstBody predecessor secondBody
        (Just 1, [predecessor], Just 0, []) => lowerUnary False context env family result secondBody predecessor firstBody
        _ => Right Nothing
    walk context env [] [] (Pi Linear family@(SeqType _ element) result) =
      case (sequenceConstructorTag globals context family element first, firstBinder,
            sequenceConstructorTag globals context family element second, secondBinder) of
        (Just 0, [], Just 1, [head, tail]) => lower context env family element result firstBody head tail secondBody
        (Just 1, [head, tail], Just 0, []) => lower context env family element result secondBody head tail firstBody
        _ => Right Nothing
    walk context env (token :: rest) ((_, _) :: modes) (Pi Erased domain result) = do
      following <- walk (Extend context Erased domain) (token.spelling :: env) rest modes result
      Right (map (Lambda Erased domain) following)
    walk context env (token :: rest) ((False, _) :: modes) (Pi Unrestricted domain result) = do
      following <- walk (Extend context Unrestricted domain) (token.spelling :: env) rest modes result
      Right (map (Lambda Unrestricted domain) following)
    walk _ _ _ _ _ = Right Nothing
private
uniformStructuralEquation : List Weighted -> String -> Nat -> Term 0 -> Expr -> Either ResolveError (Maybe (Term 0))
uniformStructuralEquation globals name implicitCount ty (NEquationLambda _ names _
  (NDataCase span (NRef _ scrutinee) Nothing [(first, firstBinder, firstBody), (second, secondBinder, secondBody)])) =
  case reverse names of
    [] => Right Nothing
    argument :: backwards =>
      uniformStructuralCandidate globals name implicitCount ty span scrutinee first firstBinder firstBody second secondBinder secondBody argument (reverse backwards)
uniformStructuralEquation _ _ _ _ _ = Right Nothing

private
legacyRecursiveEquationReserve : String -> Expr -> Nat
-- Reserve for admitted result-type copies in the closed branch contexts,
-- motive, lambda annotation and their weakening, before any are built.
legacyRecursiveEquationReserve name (NEquationLambda _ [argument] _ (NDataCase _ _ Nothing [(first, firstBinder, firstBody), (second, secondBinder, secondBody)])) =
  let natShape = (first.spelling == "Zero" && second.spelling == "Succ") ||
                 (first.spelling == "Succ" && second.spelling == "Zero")
      recursiveShape = case (firstBinder, secondBinder) of
        ([], [predecessor]) => structuralCallPresent name predecessor.spelling secondBody
        ([predecessor], []) => structuralCallPresent name predecessor.spelling firstBody
        _ => False
      sequenceShape = case (firstBinder, secondBinder) of
        ([], [_, tail]) => structuralCallPresent name tail.spelling secondBody
        ([_, tail], []) => structuralCallPresent name tail.spelling firstBody
        _ => False in
    if sequenceShape then 32 + 16 * 513 else if natShape || recursiveShape then 16 + 9 * 513 else 0
legacyRecursiveEquationReserve name (NEquationLambda _ [_, _] _ (NDataCase _ _ Nothing [(_, firstBinder, firstBody), (_, secondBinder, secondBody)])) =
  let shape = case (firstBinder, secondBinder) of
        ([], [_, tail]) => polymorphicCallPresent name tail.spelling secondBody
        ([_, tail], []) => polymorphicCallPresent name tail.spelling firstBody
        _ => False in
    if shape then 64 + 24 * 513 else 0
legacyRecursiveEquationReserve _ _ = 0

private
uniformEquationReserve : String -> Expr -> Nat
uniformEquationReserve name (NEquationLambda _ names signature (NDataCase _ _ Nothing [(_, firstBinder, firstBody), (_, secondBinder, secondBody)])) =
  case reverse names of
    [] => 0
    (_ :: backwards) =>
      let params = reverse backwards
          count = implicitPrefixCount signature
          reversed = reverse (prefixModes count params)
          shape = case (firstBinder, secondBinder) of
            ([], [_, tail]) => uniformCallPresent name reversed tail.spelling secondBody
            ([_, tail], []) => uniformCallPresent name reversed tail.spelling firstBody
            ([], [tail]) => uniformCallPresent name reversed tail.spelling secondBody
            ([tail], []) => uniformCallPresent name reversed tail.spelling firstBody
            _ => False in
        if length params <= 64 && count <= length params && shape
          then 128 + (40 + length params) * 513 else 0
uniformEquationReserve _ _ = 0

private
recursiveEquationReserve : String -> Expr -> Nat
recursiveEquationReserve name expression =
  max (accumulatorReserve name expression) (max (legacyRecursiveEquationReserve name expression) (uniformEquationReserve name expression))
  where
    -- Reserve up to 20 guarded 513-node copies for the family, element,
    -- distinct accumulator, continuation and annotations. The authored
    -- update's expansion is included separately in the source cost.
    accumulatorReserve : String -> Expr -> Nat
    accumulatorReserve name (NEquationLambda _ [argument, accumulator] _ (NDataCase _ _ Nothing [(first, firstBinder, firstBody), (second, secondBinder, secondBody)])) =
      let shape = case (firstBinder, secondBinder) of
            ([], [head, tail]) => isJust (accumulatorCall name tail.spelling secondBody)
            ([head, tail], []) => isJust (accumulatorCall name tail.spelling firstBody)
            _ => False in
        if shape then 64 + 20 * 513 else 0
    accumulatorReserve _ _ = 0

-- Recover only authored Name tokens for the successfully admitted occurrences.
-- Grouped expression spans can include punctuation and are not navigation spans.
private
structuralNameSpans : String -> Expr -> List SourceSpan -> List SourceSpan
structuralNameSpans name (NRef span ref) rest = if ref == name then span :: rest else rest
structuralNameSpans name (NApply _ function argument) rest =
  structuralNameSpans name function (structuralNameSpans name argument rest)
structuralNameSpans name (NImplicitApply _ function argument) rest =
  structuralNameSpans name function (structuralNameSpans name argument rest)
structuralNameSpans name (NIf _ condition yes no) rest =
  structuralNameSpans name condition (structuralNameSpans name yes (structuralNameSpans name no rest))
structuralNameSpans _ _ rest = rest

private
structuralSites : ModuleSnapshot -> Declaration -> List RecursiveSite
structuralSites snapshot decl = case decl.value of
  NEquationLambda _ _ _ (NDataCase _ _ _ arms) =>
    let spans = branchNames arms
        tokens = snapshot.document.tokens in
      collect (S (length spans + length tokens)) spans tokens
  _ => []
  where
    branchNames : List (Token, List Token, Expr) -> List SourceSpan
    branchNames [] = []
    branchNames ((_, _, body) :: rest) = structuralNameSpans decl.name body (branchNames rest)

    -- Both lists are in authored order. Advance at least one per step instead
    -- of rescanning the complete token stream for each recursive reference.
    collect : Nat -> List SourceSpan -> List Token -> List RecursiveSite
    collect Z _ _ = []
    collect (S fuel) [] _ = []
    collect (S fuel) _ [] = []
    collect (S fuel) spans@(span :: rest) tokens@(token :: later) =
      if token.span.start.offset >= span.finish.offset then collect fuel rest tokens else
      if token.span.finish.offset <= span.start.offset then collect fuel spans later else
      if token.kind == Name && token.spelling == decl.name &&
         token.span.start.offset >= span.start.offset && token.span.finish.offset <= span.finish.offset
        then StructuralSite snapshot.path token.span decl.definitionNameSpan :: collect fuel rest later
        else collect fuel spans later

compileDeclarations : ModuleSnapshot -> List String -> List Weighted -> List Declaration -> Nat ->
                      Either GraphError Compiled
compileDeclarations snapshot name globals [] remaining = Right (Definitions [] [] [] remaining)
compileDeclarations snapshot name globals (decl :: rest) remaining = do
  if decl.quantity == Linear || decl.name == "_"
     then Left (problem snapshot (Just decl.nameSpan.start)
                "Module globals require erased/unrestricted quantities and referenceable names")
     else Right ()
  if decl.dictionary && decl.quantity /= Unrestricted
     then Left (problem snapshot (Just decl.nameSpan.start) "Implementations require unrestricted named dictionary values") else Right ()
  let estimate = cost remaining globals [] decl.expected + cost remaining globals [] decl.value + recursiveEquationReserve decl.name decl.value
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
  recursive <- case natRecursiveEquation globals decl.name ty decl.value of
    Left err => Left ({ stage := if err.elaborating then "elaboration" else "resolution" } (problem snapshot (Just err.position) (show err)))
    Right candidate => Right candidate
  recursive <- the (Either GraphError (Maybe (Term 0))) $ case recursive of
    Just result => Right (Just result)
    Nothing => case unaryRecursiveEquation globals decl.name ty decl.value of
      Left err => Left ({ stage := if err.elaborating then "elaboration" else "resolution" } (problem snapshot (Just err.position) (show err)))
      Right candidate => Right candidate
  recursive <- the (Either GraphError (Maybe (Term 0))) $ case recursive of
    Just result => Right (Just result)
    Nothing => case sequenceRecursiveEquation globals decl.name ty decl.value of
      Left err => Left ({ stage := if err.elaborating then "elaboration" else "resolution" } (problem snapshot (Just err.position) (show err)))
      Right candidate => Right candidate
  recursive <- the (Either GraphError (Maybe (Term 0))) $ case recursive of
    Just result => Right (Just result)
    Nothing => case accumulatorSequenceEquation globals decl.name ty decl.value of
      Left err => Left ({ stage := if err.elaborating then "elaboration" else "resolution" } (problem snapshot (Just err.position) (show err)))
      Right candidate => Right candidate
  recursive <- the (Either GraphError (Maybe (Term 0))) $ case recursive of
    Just result => Right (Just result)
    Nothing => case polymorphicSequenceEquation globals decl.name (implicitPrefix == 1) ty decl.value of
      Left err => Left ({ stage := if err.elaborating then "elaboration" else "resolution" } (problem snapshot (Just err.position) (show err)))
      Right candidate => Right candidate
  recursive <- the (Either GraphError (Maybe (Term 0))) $ case recursive of
    Just result => Right (Just result)
    Nothing => case uniformStructuralEquation globals decl.name implicitPrefix ty decl.value of
      Left err => Left ({ stage := if err.elaborating then "elaboration" else "resolution" } (problem snapshot (Just err.position) (show err)))
      Right candidate => Right candidate
  value <- case recursive of
    Just recursive => Right recursive
    Nothing => case elaborateExpected (map global globals) Empty [] ty decl.value of
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
  let definition = GlobalEntry (if provider then Just identity else Nothing) (Just identity) implicitPrefix decl.quantity decl.name ty value
  let local = weighted definition
  let qualified = Weight ({ name := identity } definition) local.size
  following <- compileDeclarations snapshot name (local :: qualified :: globals) rest (minus remaining estimate)
  let ownSites = case recursive of
        Just _ => structuralSites snapshot decl
        Nothing => []
  Right (Definitions (local :: following.locals)
           (if decl.exported then qualified :: following.exports else following.exports)
           (ownSites ++ following.sites) following.remaining)

shortName : String -> String
shortName name = case reverse (forget (Data.String.split (== '.') name)) of
  [] => name
  part :: _ => part


selectedSchema : List Weighted -> InterfaceSchema -> InterfaceSchema
selectedSchema bindings schema =
  { constructorVisible := any (\binding => binding.global.name == schema.constructorName &&
      binding.global.canonicalName == Just schema.constructorOrigin) bindings } schema

-- Validate against checked exports once; all visibility paths consume this view.
filteredImports : ModuleSnapshot -> List Interface -> Either GraphError (List Interface)
filteredImports snapshot interfaces = traverse select snapshot.document.imports
  where
    validate : List Weighted -> List String -> List Token -> Either GraphError ()
    validate bindings seen [] = Right ()
    validate bindings seen (selector :: rest) = do
      if elem selector.spelling seen
        then Left (problem snapshot (Just selector.span.start) "Duplicate import selector") else Right ()
      if any (\entry => shortName entry.global.name == selector.spelling) bindings
        then validate bindings (selector.spelling :: seen) rest
        else Left (problem snapshot (Just selector.span.start) "Import selector is not a checked export")

    select : ImportDeclaration -> Either GraphError Interface
    select dependency = case find (\entry => entry.name == dependency.components) interfaces of
      Nothing => Left (problem snapshot (Just dependency.span.start) "Missing checked dependency interface")
      Just entry => case dependency.selectors of
        Nothing => Right entry
        Just selectors => do
          validate entry.bindings [] selectors
          let names = map spelling selectors
          let bindings = filter (\binding => elem (shortName binding.global.name) names) entry.bindings
          let schemas = map (selectedSchema bindings)
                        (filter (\schema => elem (shortName schema.name) names) entry.schemas)
          Right ({ bindings := bindings, schemas := schemas } entry)

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

importAliases : List Weighted -> List Weighted
importAliases imported = mapMaybe alias groups
  where
    named : List (String, Weighted)
    named = map (\entry => (shortName entry.global.name, entry)) imported

    groups : List (List1 (String, Weighted))
    groups = groupBy (\a, b => fst a == fst b) (sortBy (\a, b => compare (fst a) (fst b)) named)

    alias : List1 (String, Weighted) -> Maybe Weighted
    alias group = case forget group of
      [] => Nothing
      ((name, entry) :: rest) =>
        if all (\(_, other) => other.global.canonicalName == entry.global.canonicalName) rest
          then Just ({ global := { name := name, provider := Nothing } entry.global } entry)
          else Nothing

qualifiedImportAliases : ModuleSnapshot -> List Interface -> List Weighted
qualifiedImportAliases snapshot interfaces = concatMap aliases snapshot.document.imports
  where
    aliases : ImportDeclaration -> List Weighted
    aliases dependency = case (dependency.alias, find (\entry => entry.name == dependency.components) interfaces) of
      (Just alias, Just entry) => map (\binding =>
        { global := { name := alias.spelling ++ "." ++ shortName binding.global.name, provider := Nothing } binding.global } binding) entry.bindings
      _ => []

schemaAlias : SortedSet String -> InterfaceSchema -> Maybe InterfaceSchema
schemaAlias aliases schema =
  let name = shortName schema.name in
  if Data.SortedSet.contains name aliases
    then Just ({ name := name } schema) else Nothing

-- Resolve constructor availability across all selected direct imports by checked
-- canonical identity, rather than selecting an import path by list order.
visibleSchema : SortedMap String String -> InterfaceSchema -> InterfaceSchema
visibleSchema constructors schema = case Data.SortedMap.lookup schema.constructorOrigin constructors of
  Nothing => { constructorVisible := False } schema
  Just name => { constructorName := name, constructorVisible := True } schema

directSchemas : ModuleSnapshot -> List Interface -> List Weighted -> List Weighted -> List InterfaceSchema
directSchemas snapshot interfaces aliases imported =
  let constructors = Data.SortedMap.fromList (mapMaybe (\entry => map (\origin => (origin, entry.global.name)) entry.global.canonicalName) imported)
      schemas = concatMap (\dependency =>
        case find (\entry => entry.name == dependency.components) interfaces of
          Nothing => []
          Just entry => map (visibleSchema constructors) entry.schemas) snapshot.document.imports
      qualifiedSchemas = concatMap (\dependency =>
        case (dependency.alias, find (\entry => entry.name == dependency.components) interfaces) of
          (Just alias, Just entry) => map (\schema => { name := alias.spelling ++ "." ++ shortName schema.name } (visibleSchema constructors schema)) entry.schemas
          _ => []) snapshot.document.imports
      aliasNames = Data.SortedSet.fromList (map (\entry => entry.global.name) aliases)
   in schemas ++ qualifiedSchemas ++ mapMaybe (schemaAlias aliasNames) schemas

-- Publish only selected checked bindings, preserving their canonical origins.
publicBindings : ModuleSnapshot -> List Interface -> List Weighted -> Either GraphError (List Weighted)
publicBindings snapshot interfaces locals = collect [] snapshot.document.imports
  where
    collect : List Weighted -> List ImportDeclaration -> Either GraphError (List Weighted)
    collect published [] = Right published
    collect published (dependency :: rest) = case dependency.publicMarker of
      Nothing => collect published rest
      Just marker => case find (\entry => entry.name == dependency.components) interfaces of
        Nothing => Left (problem snapshot (Just marker.span.start) "Missing checked dependency interface")
        Just entry => do
          let bindings = entry.bindings
          next <- add published bindings
          collect next rest
      where
        add : List Weighted -> List Weighted -> Either GraphError (List Weighted)
        add seen [] = Right seen
        add seen (binding :: remaining) = do
          let name = shortName binding.global.name
          let matches = filter (\existing => shortName existing.global.name == name) (locals ++ seen)
          if any (\existing => existing.global.canonicalName /= binding.global.canonicalName) matches
            then Left (problem snapshot (map (\selector => selector.span.start) (find (\selector => selector.spelling == name) (fromMaybe [] dependency.selectors))) ("Conflicting public export " ++ name))
            else if null matches
              then add (binding :: seen) remaining
              else add seen remaining

-- Rebase only selected public interface schemas. Their constructor is visible
-- only if the facade actually publishes the same checked constructor origin.
publicSchemas : List String -> ModuleSnapshot -> List Interface -> List Weighted -> List InterfaceSchema
publicSchemas moduleName snapshot interfaces published =
  nubBy (\a, b => a.name == b.name && a.constructorOrigin == b.constructorOrigin)
    (concatMap fromImport snapshot.document.imports)
  where
    rebase : InterfaceSchema -> InterfaceSchema
    rebase schema =
      let constructor = moduleText moduleName ++ "." ++ shortName schema.constructorName in
      { name := moduleText moduleName ++ "." ++ shortName schema.name,
        constructorName := constructor,
        constructorVisible := any (\binding => binding.global.name == constructor &&
          binding.global.canonicalName == Just schema.constructorOrigin) published } schema

    fromImport : ImportDeclaration -> List InterfaceSchema
    fromImport dependency = case dependency.publicMarker of
      Nothing => []
      Just _ => case find (\entry => entry.name == dependency.components) interfaces of
        Nothing => []
        Just entry => map rebase entry.schemas

elaborateAt : ModuleSnapshot -> List InterfaceSchema -> List String -> List AuthoredDeclaration -> Either GraphError (List Declaration)
elaborateAt snapshot schemas imported authored = case elaborateDeclarationsInWithImports
  (map (\header => moduleText header.components) snapshot.document.moduleHeader) schemas imported 64 authored of
  Left err => Left ({ stage := "elaboration" } (problem snapshot (Just err.position) err.message))
  Right declarations => Right declarations

anonymous : ModuleSnapshot -> List InterfaceSchema -> List Weighted -> Nat -> Either GraphError (Term 0)
anonymous snapshot schemas globals remaining = do
  expression <- case snapshot.document.body of
    EmptyDocument => Left (problem snapshot Nothing "Entry requires an expression or main")
    ExpressionDocument expression => Right expression
    DeclarationDocument authored => do
      declarations <- elaborateAt snapshot schemas [] authored
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

compileGraph : Bool -> ModuleGraph -> List Weighted -> List Interface -> Nat -> List RecursiveSite -> List ModuleSnapshot ->
               Either GraphError (Maybe CheckedProject, List (List String, List (String, String)), List RecursiveSite)
compileGraph requireEntry graph prelude interfaces remaining sites [] =
  if requireEntry then Left (GraphFailure graph.entry "" Nothing "No entry snapshot in graph")
    else Right (Nothing, exportIndex interfaces, sites)
compileGraph requireEntry graph prelude interfaces remaining sites (snapshot :: rest) = do
  if requireEntry && snapshot.path == graph.entry && not (null rest)
     then Left (problem snapshot Nothing "Entry snapshot must be last in dependency order")
     else Right ()
  visibleInterfaces <- filteredImports snapshot interfaces
  imported <- directImports snapshot visibleInterfaces
  if length imported > 4096 then Left (problem snapshot Nothing "Imported binding budget exhausted (4096)") else Right ()
  let aliases = importAliases imported
  let schemas = directSchemas snapshot visibleInterfaces aliases imported
  -- Imports shadow Prelude names; ambiguous imports must not silently fall
  -- back to a Prelude definition. Local declarations are prepended later.
  let importedNames = Data.SortedSet.fromList (map (\entry => shortName entry.global.name) imported)
  let visiblePrelude = filter (\entry => not (Data.SortedSet.contains entry.global.name importedNames)) prelude
  let globals = imported ++ qualifiedImportAliases snapshot visibleInterfaces ++ aliases ++ visiblePrelude
  case snapshot.document.moduleHeader of
    Nothing => if not requireEntry || snapshot.path /= graph.entry then Left (problem snapshot Nothing "Anonymous dependency") else do
      term <- anonymous snapshot schemas globals remaining
      case inferRuntime checkingDepth typeReductionFuel Empty term of
        Left err => Left ({ stage := "runtime-checking" } (problem snapshot Nothing ("Entry checking: " ++ show err)))
        Right checked => Right (Just (Project graph term checked.inferredType sites (exportIndex interfaces)), exportIndex interfaces, sites)
    Just header => do
      if any (\entry => entry.name == header.components) interfaces
         then Left (problem snapshot (Just header.nameSpan.start) "Duplicate checked module identity")
         else Right ()
      declarations <- case snapshot.document.body of
        DeclarationDocument authored => elaborateAt snapshot schemas (map (\entry => entry.global.name) imported) authored
        EmptyDocument => Right []
        _ => Left (problem snapshot Nothing "Named modules require declarations")
      compiled <- compileDeclarations snapshot header.components globals declarations remaining
      published <- publicBindings snapshot visibleInterfaces compiled.exports
      if length published + length compiled.exports > 4096
        then Left (problem snapshot Nothing "Export binding budget exhausted (4096)") else Right ()
      let rebased = map (\entry => { global := { name := moduleText header.components ++ "." ++ shortName entry.global.name } entry.global } entry) published
      case graph.scope of
        PackageRoots _ _ _ => if header.components == ["Main"] then do
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
              Right checked => Right (Just (Project graph term checked.inferredType (sites ++ compiled.sites) (exportIndex interfaces)), exportIndex interfaces, sites ++ compiled.sites)
         else let visible = case snapshot.document.body of
                    DeclarationDocument authored => exportedSchemas (moduleText header.components) authored
                    _ => []
               in let dataHints = case snapshot.document.body of
                        DeclarationDocument authored => exportedDataSchemas (moduleText header.components) authored
                        _ => []
                   in let publishedSchemas = publicSchemas header.components snapshot visibleInterfaces (compiled.exports ++ rebased)
                   in compileGraph requireEntry graph prelude (Exports header.components (compiled.exports ++ rebased) (visible ++ publishedSchemas) dataHints :: interfaces)
                           compiled.remaining (sites ++ compiled.sites) rest

||| Check every dependency declaration before exposing its qualified exports.
||| Expansion budget concerns elaboration, not normalization/allocation/time bounds.
public export
checkModuleGraph : ModuleGraph -> Either GraphError CheckedProject
checkModuleGraph graph = do
  prelude <- case preludeGlobals of
    Left err => Left ({ stage := "prelude" } (GraphFailure graph.entry "" Nothing ("Bundled prelude: " ++ err)))
    Right globals => Right (map weighted globals)
  (checked, _, _) <- compileGraph True graph prelude [] 200000 [] graph.modules
  case checked of
    Just project => Right project
    Nothing => Left (GraphFailure graph.entry "" Nothing "Missing checked entry")

||| Inventory checking retains checked exports and structural recursion sites.
public export
checkInventoryNavigation : ModuleGraph -> Either GraphError (List (List String, List (String, String)), List RecursiveSite)
checkInventoryNavigation graph = do
  prelude <- case preludeGlobals of
    Left err => Left ({ stage := "prelude" } (GraphFailure graph.root "" Nothing (show err)))
    Right globals => Right (map weighted globals)
  (_, exports, sites) <- compileGraph False graph prelude [] 200000 [] graph.modules
  Right (exports, sites)

public export
checkInventoryExports : ModuleGraph -> Either GraphError (List (List String, List (String, String)))
checkInventoryExports graph = map fst (checkInventoryNavigation graph)

public export
checkInventoryGraph : ModuleGraph -> Either GraphError ()
checkInventoryGraph graph = map (const ()) (checkInventoryExports graph)

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
