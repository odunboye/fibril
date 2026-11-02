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

expose : Position -> Term n -> Either ResolveError (Term n)
expose position ty = case weakHead typeReductionFuel ty of
  HeadForm result => Right result
  HeadLimit _ => Left (CannotElaborate position "Dictionary type exposure exhausted its reduction budget")

public export
dictionaryType : Position -> Term n -> Either ResolveError ()
dictionaryType position ty = do
  head <- expose position ty
  case head of
    BoxType _ _ => Right ()
    Sigma _ _ _ _ => Right ()
    _ => Left (CannotElaborate position "Constraint/selection requires a dictionary-shaped unary or dependent-pair type")

public export
constraintType : Position -> Quantity -> Term n -> Either ResolveError ()
constraintType position Erased ty = Left (CannotElaborate position "Dictionary constraints require linear or unrestricted runtime permission")
constraintType position _ ty = dictionaryType position ty

nextDictionary : Position -> Context n -> Term n -> Either ResolveError (Term n)
nextDictionary position context function = do
  ty <- case inferErased checkingDepth typeReductionFuel context function of
    Left err => Left (CannotElaborate position ("Cannot infer dictionary function type: " ++ show err))
    Right ty => expose position ty
  case ty of
    Pi q domain _ => do
      constraintType position q domain
      Right domain
    _ => Left (CannotElaborate position "Dictionary selection requires a function with a dictionary argument")

entries : Vect n String -> List (String, Fin n)
entries [] = []
entries (name :: rest) = (name, FZ) :: map (\(name, index) => (name, FS index)) (entries rest)

candidates : Position -> Context n -> Term n -> List String -> List (String, Fin n) ->
             Either ResolveError (List (Fin n))
candidates position context expected seen [] = Right []
candidates position context expected seen ((name, index) :: rest) =
  if name == "_" || elem name seen then candidates position context expected seen rest else do
    let following = name :: seen
    if not (allows (lookupQuantity index context) Linear)
       then candidates position context expected following rest else do
         ty <- expose position (lookupType index context)
         eligible <- case ty of
           BoxType _ _ => Right True
           Sigma _ _ _ _ => Right True
           _ => Right False
         matches <- if eligible then case betaCompare typeReductionFuel ty expected of
           EqualNormalForms => Right True
           DifferentNormalForms => Right False
           Inconclusive => Left (CannotElaborate position "Local dictionary comparison exhausted its reduction budget")
           else Right False
         remaining <- candidates position context expected following rest
         Right (if matches then index :: remaining else remaining)

globalCandidates : Position -> Term n -> List String -> List GlobalDefinition ->
                   Either ResolveError (List GlobalDefinition)
globalCandidates position expected seen [] = Right []
globalCandidates position expected seen (entry :: rest) = case entry.provider of
  Nothing => globalCandidates position expected seen rest
  Just identity =>
    if elem identity seen || entry.quantity /= Unrestricted
       then globalCandidates position expected seen rest else do
         matches <- case betaCompare typeReductionFuel (rename absurd entry.declaredType) expected of
           EqualNormalForms => Right True
           DifferentNormalForms => Right False
           Inconclusive => Left (CannotElaborate position "Visible implementation comparison exhausted its reduction budget")
         remaining <- globalCandidates position expected (identity :: seen) rest
         Right (if matches then entry :: remaining else remaining)

||| Opt-in finite lookup of already checked visible named implementation values.
public export
selectImplementation : Position -> List GlobalDefinition -> Context n -> Term n ->
                       Either ResolveError (Term n)
selectImplementation position globals context function = do
  expected <- nextDictionary position context function
  available <- globalCandidates position expected [] globals
  case available of
    [entry] => case lookupGlobal entry.name [entry] of
      Nothing => Left (CannotElaborate position "Visible implementation has no runtime occurrence")
      Just value => Right (Apply function (rename absurd value))
    [] => Left (CannotElaborate position "No matching visible named implementation; supply @{dictionary} explicitly")
    _ => Left (CannotElaborate position "Ambiguous visible named implementations; supply @{dictionary} explicitly")

public export
selectDictionary : Position -> Context n -> Vect n String -> Term n -> Maybe (Term n) ->
                   Either ResolveError (Term n)
selectDictionary position context names function explicit = do
  expected <- nextDictionary position context function
  argument <- case explicit of
    Just value => do
      actual <- case inferErased checkingDepth typeReductionFuel context value of
        Left err => Left (CannotElaborate position ("Invalid explicit dictionary: " ++ show err))
        Right ty => Right ty
      case compatibleTypes typeReductionFuel actual expected of
        Compatible => Right value
        Incompatible => Left (CannotElaborate position "Explicit dictionary does not match the required type")
        CompatibilityLimit => Left (CannotElaborate position "Explicit dictionary comparison exhausted its reduction budget")
    Nothing => do
      available <- candidates position context expected [] (entries names)
      case available of
        [index] => Right (Variable index)
        [] => Left (CannotElaborate position "No matching visible local dictionary; supply @{dictionary} explicitly")
        _ => Left (CannotElaborate position "Ambiguous local dictionaries; supply @{dictionary} explicitly")
  Right (Apply function argument)
