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

walk : Walker destination -> Environment destination -> Expr -> List (ReferenceTo destination)
walk context env (NRef span name) =
  let target = case lexicalTarget name env of
        Just target => Just target
        Nothing => if any (\entry => fst entry == name) env then Nothing else context.globalTarget name
   in case (nameToken name span context.tokens, target) of
    (Just origin, Just target) => [RefersTo origin target]
    _ => []
-- Only the final identifier is selectable, not module qualifiers or dots.
walk context env (NQualifiedRef region name) =
  case (find (\token => token.kind == Name &&
                      token.span.start.offset >= region.start.offset &&
                      token.span.finish.offset <= region.finish.offset) (reverse context.tokens),
        context.qualifiedTarget name) of
    (Just token, Just target) => [RefersTo token.span target]
    _ => []
walk context env (NSort _ _) = []
walk context env (NUnitType _) = []
walk context env (NUnitValue _) = []
walk context env (NStringType _) = []
walk context env (NStringValue _ _) = []
walk context env (NBoolType _) = []
walk context env (NBoolValue _ _) = []
walk context env (NIf _ condition yes no) =
  walk context env condition ++ walk context env yes ++ walk context env no
walk context env (NUnitCase _ value body) = walk context env value ++ walk context env body
walk context env (NSigma span q r name domain body) =
  let target = binderToken name span domain context.tokens
   in walk context env domain ++ self context target ++ walk context ((name, map context.localTarget target) :: env) body
walk context env (NPairValue _ ty first second) = walk context env ty ++ walk context env first ++ walk context env second
walk context env (NPairCase _ motive value branch) = walk context env motive ++ walk context env value ++ walk context env branch
walk context env (NPi span q name domain body) =
  let target = binderToken name span domain context.tokens
   in walk context env domain ++ self context target ++ walk context ((name, map context.localTarget target) :: env) body
walk context env (NLambda span q name domain body) =
  let target = binderToken name span domain context.tokens
   in walk context env domain ++ self context target ++ walk context ((name, map context.localTarget target) :: env) body
walk context env (NApply _ function argument) = walk context env function ++ walk context env argument
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

declarations : Walker destination -> Environment destination -> List AuthoredDeclaration -> List (ReferenceTo destination)
declarations context env [] = []
declarations context env (Ordinary decl :: rest) =
  (if decl.name == "_" then [] else if decl.generated then
    [RefersTo decl.nameSpan (context.localTarget decl.definitionNameSpan)] else
    [RefersTo decl.nameSpan (context.localTarget decl.definitionNameSpan),
     RefersTo decl.definitionNameSpan (context.localTarget decl.definitionNameSpan)]) ++
  (if decl.generated then [] else walk context env decl.expected ++ walk context env decl.value) ++
  declarations context ((decl.name, Just (context.localTarget decl.definitionNameSpan)) :: env) rest

declarations context env (item@(RecordItem _) :: rest) =
  let sites = bindingSites item
      refs = map (\site => RefersTo site.nameSpan (context.localTarget site.definitionNameSpan)) sites
      following = foldl (\scope, site => (site.name, Just (context.localTarget site.definitionNameSpan)) :: scope) env sites
   in refs ++ declarations context following rest

||| Shared traversal with lexical shadowing before unqualified global lookup.
public export
documentReferencesWithGlobals : (SourceSpan -> destination) -> (String -> Maybe destination) ->
                               (String -> Maybe destination) -> ParsedDocument ->
                               List (ReferenceTo destination)
documentReferencesWithGlobals local globals qualified document =
  let context = Walking document.tokens local qualified globals
   in case document.body of
        EmptyDocument => []
        DeclarationDocument values => declarations context [] values
        ExpressionDocument value => walk context [] value

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
