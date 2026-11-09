-- Explicit requests for bounded local dictionary selection, not instance search.
module Fibril.Elaboration.Expression.Dictionary

import Data.Fin
import Data.Vect
import Data.List
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Compatibility
import Fibril.Core.Limits
import Fibril.Source.Text
import Fibril.Source.Global
import Fibril.Source.Resolve.Error

%default total

exposeGlobals : GlobalContext -> Position -> Term n -> Either ResolveError (Term n)
exposeGlobals shared position ty = case weakHeadGlobals (globalValue shared) typeReductionFuel ty of
  HeadForm result => Right result
  HeadLimit _ => Left (CannotElaborate position "Dictionary type exposure exhausted its reduction budget")

public export
dictionaryTypeGlobals : GlobalContext -> Position -> Term n -> Either ResolveError ()
dictionaryTypeGlobals shared position ty = do
  head <- exposeGlobals shared position ty
  case head of
    BoxType _ _ => Right ()
    Sigma _ _ _ _ => Right ()
    _ => Left (CannotElaborate position "Constraint/selection requires a dictionary-shaped unary or dependent-pair type")

public export
constraintTypeGlobals : GlobalContext -> Position -> Quantity -> Term n -> Either ResolveError ()
constraintTypeGlobals shared position Erased ty = Left (CannotElaborate position "Dictionary constraints require linear or unrestricted runtime permission")
constraintTypeGlobals shared position _ ty = dictionaryTypeGlobals shared position ty

nextDictionaryGlobals : GlobalContext -> Position -> Context n -> Term n -> Either ResolveError (Term n)
nextDictionaryGlobals shared position context function = do
  ty <- case inferErasedGlobals shared checkingDepth typeReductionFuel context function of
    Left err => Left (CannotElaborate position ("Cannot infer dictionary function type: " ++ show err))
    Right ty => exposeGlobals shared position ty
  case ty of
    Pi q domain _ => do
      constraintTypeGlobals shared position q domain
      Right domain
    _ => Left (CannotElaborate position "Dictionary selection requires a function with a dictionary argument")

entries : Vect n String -> List (String, Fin n)
entries [] = []
entries (name :: rest) = (name, FZ) :: map (\(name, index) => (name, FS index)) (entries rest)

candidatesGlobals : GlobalContext -> Position -> Context n -> Term n -> List String -> List (String, Fin n) ->
             Either ResolveError (List (Fin n))
candidatesGlobals shared position context expected seen [] = Right []
candidatesGlobals shared position context expected seen ((name, index) :: rest) =
  if name == "_" || elem name seen then candidatesGlobals shared position context expected seen rest else do
    let following = name :: seen
    if not (allows (lookupQuantity index context) Linear)
       then candidatesGlobals shared position context expected following rest else do
         ty <- exposeGlobals shared position (lookupType index context)
         eligible <- case ty of
           BoxType _ _ => Right True
           Sigma _ _ _ _ => Right True
           _ => Right False
         matches <- if eligible then case betaCompareGlobals (globalValue shared) typeReductionFuel ty expected of
           EqualNormalForms => Right True
           DifferentNormalForms => Right False
           Inconclusive => Left (CannotElaborate position "Local dictionary comparison exhausted its reduction budget")
           else Right False
         remaining <- candidatesGlobals shared position context expected following rest
         Right (if matches then index :: remaining else remaining)

globalCandidatesGlobals : GlobalContext -> Position -> Term n -> List String -> List GlobalDefinition ->
                   Either ResolveError (List GlobalDefinition)
globalCandidatesGlobals shared position expected seen [] = Right []
globalCandidatesGlobals shared position expected seen (entry :: rest) = case entry.provider of
  Nothing => globalCandidatesGlobals shared position expected seen rest
  Just identity =>
    if elem identity seen || entry.quantity /= Unrestricted
       then globalCandidatesGlobals shared position expected seen rest else do
         matches <- case betaCompareGlobals (globalValue shared) typeReductionFuel (rename absurd entry.declaredType) expected of
           EqualNormalForms => Right True
           DifferentNormalForms => Right False
           Inconclusive => Left (CannotElaborate position "Visible implementation comparison exhausted its reduction budget")
         remaining <- globalCandidatesGlobals shared position expected (identity :: seen) rest
         Right (if matches then entry :: remaining else remaining)

||| Opt-in finite lookup of already checked visible named implementation values.
public export
selectImplementationGlobals : GlobalContext -> Position -> List GlobalDefinition -> Context n -> Term n ->
                       Either ResolveError (Term n)
selectImplementationGlobals shared position globals context function = do
  expected <- nextDictionaryGlobals shared position context function
  available <- globalCandidatesGlobals shared position expected [] globals
  case available of
    [entry] => case lookupGlobal entry.name [entry] of
      Nothing => Left (CannotElaborate position "Visible implementation has no runtime occurrence")
      Just value => Right (Apply function (rename absurd value))
    [] => Left (CannotElaborate position "No matching visible named implementation; supply @{dictionary} explicitly")
    _ => Left (CannotElaborate position "Ambiguous visible named implementations; supply @{dictionary} explicitly")

||| Fill `count` constraint binders after solved implicit arguments. The required dictionary
||| type is read from the function's own type; a unique matching local dictionary wins, else a
||| unique visible implementation. Missing or ambiguous matches fail, never guess.
public export
insertDictionariesGlobals : GlobalContext -> Position -> List GlobalDefinition -> Context n -> Vect n String ->
                            Nat -> Term n -> Either ResolveError (Term n)
insertDictionariesGlobals shared position globals context names Z function = Right function
insertDictionariesGlobals shared position globals context names (S remaining) function = do
  expected <- nextDictionaryGlobals shared position context function
  locals <- candidatesGlobals shared position context expected [] (entries names)
  argument <- case locals of
    [index] => Right (Variable index)
    _ :: _ :: _ => Left (CannotElaborate position "Ambiguous local dictionaries for an inferred constraint; supply @{dictionary} explicitly")
    [] => do
      available <- globalCandidatesGlobals shared position expected [] globals
      case available of
        [entry] => case lookupGlobal entry.name [entry] of
          Nothing => Left (CannotElaborate position "Visible implementation has no runtime occurrence")
          Just value => Right (rename absurd value)
        [] => Left (CannotElaborate position "No local dictionary or visible implementation matches an inferred constraint; supply @{dictionary} explicitly")
        _ => Left (CannotElaborate position "Ambiguous visible implementations for an inferred constraint; supply @{dictionary} explicitly")
  insertDictionariesGlobals shared position globals context names remaining (Apply function argument)

public export
selectDictionaryGlobals : GlobalContext -> Position -> Context n -> Vect n String -> Term n -> Maybe (Term n) ->
                   Either ResolveError (Term n)
selectDictionaryGlobals shared position context names function explicit = do
  expected <- nextDictionaryGlobals shared position context function
  argument <- case explicit of
    Just value => do
      actual <- case inferErasedGlobals shared checkingDepth typeReductionFuel context value of
        Left err => Left (CannotElaborate position ("Invalid explicit dictionary: " ++ show err))
        Right ty => Right ty
      case compatibleTypesGlobals (globalValue shared) typeReductionFuel actual expected of
        Compatible => Right value
        Incompatible => Left (CannotElaborate position "Explicit dictionary does not match the required type")
        CompatibilityLimit => Left (CannotElaborate position "Explicit dictionary comparison exhausted its reduction budget")
    Nothing => do
      available <- candidatesGlobals shared position context expected [] (entries names)
      case available of
        [index] => Right (Variable index)
        [] => Left (CannotElaborate position "No matching visible local dictionary; supply @{dictionary} explicitly")
        _ => Left (CannotElaborate position "Ambiguous local dictionaries; supply @{dictionary} explicitly")
  Right (Apply function argument)

-- Closed-syntax compatibility APIs. Shared programs pass their checked context explicitly.
public export
constraintType : Position -> Quantity -> Term n -> Either ResolveError ()
constraintType = constraintTypeGlobals emptyGlobals

public export
dictionaryType : Position -> Term n -> Either ResolveError ()
dictionaryType = dictionaryTypeGlobals emptyGlobals

public export
selectDictionary : Position -> Context n -> Vect n String -> Term n -> Maybe (Term n) ->
                   Either ResolveError (Term n)
selectDictionary = selectDictionaryGlobals emptyGlobals

public export
selectImplementation : Position -> List GlobalDefinition -> Context n -> Term n ->
                       Either ResolveError (Term n)
selectImplementation = selectImplementationGlobals emptyGlobals
