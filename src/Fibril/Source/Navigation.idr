-- Same-document lexical navigation; not type checking or cross-file resolution.
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
record Reference where
  constructor RefersTo
  origin : SourceSpan
  target : SourceSpan

Environment : Type
Environment = List (String, Maybe SourceSpan)

lexicalTarget : String -> Environment -> Maybe SourceSpan
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

self : Maybe SourceSpan -> List Reference
self Nothing = []
self (Just span) = [RefersTo span span]

walk : List Token -> Environment -> Expr -> List Reference
walk tokens env (NRef span name) =
  case (nameToken name span tokens, lexicalTarget name env) of
    (Just origin, Just target) => [RefersTo origin target]
    _ => []
walk tokens env (NSort _ _) = []
walk tokens env (NUnitType _) = []
walk tokens env (NUnitValue _) = []
walk tokens env (NStringType _) = []
walk tokens env (NStringValue _ _) = []
walk tokens env (NBoolType _) = []
walk tokens env (NBoolValue _ _) = []
walk tokens env (NIf _ condition yes no) =
  walk tokens env condition ++ walk tokens env yes ++ walk tokens env no
walk tokens env (NUnitCase _ value body) = walk tokens env value ++ walk tokens env body
walk tokens env (NPi span q name domain body) =
  let target = binderToken name span domain tokens
   in walk tokens env domain ++ self target ++ walk tokens ((name, target) :: env) body
walk tokens env (NLambda span q name domain body) =
  let target = binderToken name span domain tokens
   in walk tokens env domain ++ self target ++ walk tokens ((name, target) :: env) body
walk tokens env (NApply _ function argument) = walk tokens env function ++ walk tokens env argument
walk tokens env (NSequence _ first rest) = walk tokens env first ++ walk tokens env rest
walk tokens env (NDoBind span name domain action body) =
  let target = binderToken name span domain tokens
   in walk tokens env domain ++ walk tokens env action ++ self target ++
      walk tokens ((name, target) :: env) body
walk tokens env (NDoResult _ result body) = walk tokens env result ++ walk tokens env body
walk tokens env (NAscribe _ term expected) = walk tokens env term ++ walk tokens env expected
walk tokens env (NLet span q name domain value body) =
  let target = binderToken name span domain tokens
   in walk tokens env domain ++ walk tokens env value ++ self target ++
      walk tokens ((name, target) :: env) body

declarations : List Token -> Environment -> List Declaration -> List Reference
declarations tokens env [] = []
declarations tokens env (decl :: rest) =
  (if decl.name == "_" then [] else
    [RefersTo decl.nameSpan decl.definitionNameSpan,
     RefersTo decl.definitionNameSpan decl.definitionNameSpan]) ++
  walk tokens env decl.expected ++ walk tokens env decl.value ++
  declarations tokens ((decl.name, Just decl.definitionNameSpan) :: env) rest

||| Source-order, nonrecursive declarations and nearest lexical binders only.
||| Unresolved/prelude names have no local target. No type-checking claim.
public export
documentReferences : String -> Either SymbolError (List Reference)
documentReferences source = do
  document <- parseDocument 64 256 source
  case document.body of
    EmptyDocument => Right []
    DeclarationDocument values => Right (declarations document.tokens [] values)
    ExpressionDocument value => Right (walk document.tokens [] value)

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
