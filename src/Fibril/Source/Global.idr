-- Closed global definitions, not axioms or trusted typing certificates.
module Fibril.Source.Global

import Data.Fin
import Data.List1
import Data.String
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Source.Fixity

%default total

||| The prelude installs unrestricted globals; modules also admit erased globals.
||| Resolution embeds checked-ascription applications, preserving declared types.
||| Ordinary checking still validates the entire resulting term; these are not axioms.
public export
record GlobalDefinition where
  constructor StoredGlobalEntry
  provider : Maybe String
  canonicalName : Maybe String
  implicitPrefix : Nat
  quantity : Quantity
  name : String
  declaredType : Term 0
  value : Term 0
  sharedKey : Maybe Nat
  ||| Constraint binders (`=>`) right after the implicit prefix; a call fills them by lookup.
  autoConstraints : Nat
  ||| Declared operator fixity; absent means the default.
  fixity : Maybe Fixity

||| Compatibility constructor for raw, expanded source globals.
public export
GlobalEntry : Maybe String -> Maybe String -> Nat -> Quantity -> String -> Term 0 -> Term 0 -> GlobalDefinition
GlobalEntry provider canonical count quantity name ty value =
  StoredGlobalEntry provider canonical count quantity name ty value Nothing 0 Nothing

||| Resolver metadata only. The core still requires an independently checked environment.
public export
sharedGlobal : Nat -> GlobalDefinition -> GlobalDefinition
sharedGlobal key entry = { sharedKey := Just key } entry

||| Compatibility constructors do not opt ordinary globals into provider lookup.
public export
GlobalWithQuantity : Quantity -> String -> Term 0 -> Term 0 -> GlobalDefinition
GlobalWithQuantity = GlobalEntry Nothing Nothing 0

||| Existing primitive/prelude definitions remain unrestricted.
public export
Global : String -> Term 0 -> Term 0 -> GlobalDefinition
Global = GlobalWithQuantity Unrestricted

||| Qualified candidates for a short name; only used for ambiguity diagnostics.
public export
qualifiedCandidates : String -> List GlobalDefinition -> List String
qualifiedCandidates name entries = nub (map canonical (filter matches entries))
  where
    canonical : GlobalDefinition -> String
    canonical entry = fromMaybe entry.name entry.canonicalName

    matches : GlobalDefinition -> Bool
    matches entry = case reverse (forget (Data.String.split (== '.') entry.name)) of
      short :: _ :: _ => short == name
      _ => False

public export
lookupGlobal : String -> List GlobalDefinition -> Maybe (Term 0)
lookupGlobal name [] = Nothing
lookupGlobal name (entry :: rest) =
  if name == entry.name
     then case (entry.sharedKey, entry.quantity) of
       (Just key, Erased) => Just (GlobalRef key)
       (Just key, Unrestricted) => Just (GlobalRef key)
       -- The erased identity is valid in erased checking, but its body uses its
       -- erased binder once at runtime. Runtime analysis rejects that original
       -- occurrence before any normalization can remove the stage barrier.
       (Nothing, Erased) => Just (Apply (Lambda Erased entry.declaredType (Variable FZ)) entry.value)
       (Nothing, Unrestricted) => Just (Apply (Lambda Linear entry.declaredType (Variable FZ)) entry.value)
       (_, Linear) => Nothing -- No linear global ownership/initialization protocol.
     else lookupGlobal name rest
