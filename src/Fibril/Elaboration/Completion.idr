-- Read-only editor metadata from a checked local context, never typing evidence.
module Fibril.Elaboration.Completion

import Data.Fin
import Data.List
import Data.Maybe
import Data.String
import Data.Vect
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Pretty
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Source.Global
import Fibril.Source.Resolve.Error
import Fibril.Source.Text

%default total

public export
scopeProbe : String -> Bool
scopeProbe = isPrefixOf "fibrilScopeQuery_"

sourceName : String -> Bool
sourceName name = name /= "_" && not (null name) && all (\c => isAlphaNum c || c == '_' || c == '\'' || c == '.') (unpack name)

indices : Vect n a -> Vect n (Fin n)
indices [] = []
indices (_ :: rest) = FZ :: map FS (indices rest)

-- Bounded display rendering. Unknown syntax retains the ordinary core spelling.
pretty : Nat -> List GlobalDefinition -> Vect n String -> Term n -> String
pretty Z globals env term = "..."
pretty (S fuel) globals env (Variable i) = index i env
pretty (S fuel) globals env (GlobalRef key) = case find (\entry => entry.sharedKey == Just key) globals of
  Just entry => entry.name
  Nothing => "$global" ++ show key
pretty (S fuel) globals env (Universe 0) = "Type"
pretty (S fuel) globals env (Pi q domain body) =
  let name = "arg" ++ show (length env)
   in "(" ++ show q ++ " " ++ name ++ " : " ++ pretty fuel globals env domain ++ ") -> " ++ pretty fuel globals (name :: env) body
pretty (S fuel) globals env (Apply fn arg) = "(" ++ pretty fuel globals env fn ++ " " ++ pretty fuel globals env arg ++ ")"
pretty (S fuel) globals env (IOType result) = "IO " ++ pretty fuel globals env result
pretty (S fuel) globals env (SeqType key element) = key ++ " " ++ pretty fuel globals env element
pretty (S fuel) globals env (DataType key) = key
pretty (S fuel) globals env term = renderTerm term

matches : GlobalContext -> Context n -> Maybe (Term n) -> Term n -> Bool
matches shared ctx Nothing value = False
matches shared ctx (Just expected) value = case checkErasedGlobals shared 256 256 ctx value expected of
  Right () => True
  Left _ => False

locals : GlobalContext -> List GlobalDefinition -> Context n -> Vect n String -> Maybe (Term n) -> List CompletionCandidate
locals shared globals ctx env expected = go [] (toList (indices env))
  where
    go : List String -> List (Fin n) -> List CompletionCandidate
    go seen [] = []
    go seen (i :: rest) =
      let name = index i env
       in if not (sourceName name) || elem name seen then go seen rest else
          Candidate name (show (lookupQuantity i ctx) ++ " " ++ pretty 32 globals env (lookupType i ctx)) "local" Nothing
            (matches shared ctx expected (Variable i)) :: go (name :: seen) rest

globalCandidates : GlobalContext -> Context n -> Vect n String -> Maybe (Term n) -> List GlobalDefinition -> List CompletionCandidate
globalCandidates shared ctx env expected globals = go (toList env) globals
  where
    go : List String -> List GlobalDefinition -> List CompletionCandidate
    go seen [] = []
    go seen (entry :: rest) =
      if not (sourceName entry.name) || elem entry.name seen || entry.quantity == Linear then go seen rest else
        let value = fromMaybe (rename absurd entry.value) (map (rename absurd) (lookupGlobal entry.name globals))
         in Candidate entry.name (show entry.quantity ++ " " ++ pretty 32 globals [] entry.declaredType) "global" entry.canonicalName
              (matches shared ctx expected value) :: go (entry.name :: seen) rest

public export
scopeFailure : GlobalContext -> List GlobalDefinition -> Maybe (Context n) -> Vect n String -> Maybe (Term n) -> Position -> String -> ResolveError
scopeFailure shared globals Nothing env expected point name = Unbound point name
scopeFailure shared globals (Just ctx) env expected point name =
  if not (scopeProbe name) then Unbound point name else
    case checkErasedContextGlobals shared 256 256 ctx of
      Left _ => Unbound point name
      Right () => ScopedResolutionFailure point name False (ScopeAt name
        (locals shared globals ctx env expected ++ globalCandidates shared ctx env expected globals))
