-- Conservative same-document lexical rename previews; never writes source.
module Fibril.Source.Rename

import Data.List
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Symbol
import Fibril.Source.Navigation
import Fibril.Source.Syntax
import Fibril.Source.Declaration
import Fibril.Source.Document

%default total

public export
data RenameError = RenameFrontend SymbolError | InvalidRenameName
                 | NoRenameTarget | RenameEntrypoint | RenameChangesScope | RenameSizeLimit | RenameModuleUnsupported

public export
record RenamePreview where
  constructor Preview
  replacement : String
  edits : List SourceSpan

sameSpan : SourceSpan -> SourceSpan -> Bool
sameSpan a b = a.start.offset == b.start.offset && a.finish.offset == b.finish.offset

atCursor : Nat -> Nat -> Reference -> Bool
atCursor line column reference = line == reference.origin.start.line &&
  column >= reference.origin.start.column && column < reference.origin.finish.column

sourceOrder : SourceSpan -> SourceSpan -> Ordering
sourceOrder a b = compare a.start.offset b.start.offset

validName : String -> Bool
validName name = length (unpack name) <= 256 && name /= "_" && case lexSource name of
  Right [token] => token.kind == Name && token.spelling == name
  _ => False

utf8Width : Char -> Nat
utf8Width char = if ord char <= 0x7f then 1 else if ord char <= 0x7ff then 2
                else if ord char <= 0xffff then 3 else 4

byteCount : String -> Nat
byteCount text = foldl (\count, char => count + utf8Width char) 0 (unpack text)

replaceFrom : Nat -> List Char -> List Char -> List SourceSpan -> List Char
replaceFrom previous chars replacement [] = chars
replaceFrom previous chars replacement (span :: rest) =
  take (minus span.start.offset previous) chars ++ replacement ++
    replaceFrom span.finish.offset (drop (minus span.finish.offset previous) chars) replacement rest

-- Map token boundaries without signed arithmetic. Edits are ordered/disjoint.
shiftFrom : Nat -> Nat -> Nat -> Nat -> List SourceSpan -> Nat
shiftFrom offset width old new [] = new + (minus offset old)
shiftFrom offset width old new (span :: rest) =
  if offset <= span.start.offset then new + (minus offset old)
  else if offset >= span.finish.offset
    then shiftFrom offset width span.finish.offset
                   (new + (minus span.start.offset old) + width) rest
    else new + (minus span.start.offset old)

mappedSpan : Nat -> List SourceSpan -> SourceSpan -> SourceSpan -> Bool
mappedSpan width edits before after =
  shiftFrom before.start.offset width 0 0 edits == after.start.offset &&
  shiftFrom before.finish.offset width 0 0 edits == after.finish.offset

preserved : Nat -> List SourceSpan -> List Reference -> Reference -> Bool
preserved width edits after before = any
  (\reference => mappedSpan width edits before.origin reference.origin &&
                 mappedSpan width edits before.target reference.target) after

-- Without checked resolution, a final bare head and its body cannot be
-- distinguished reliably from a constructor and its uses.
ambiguousClauseTouches : String -> String -> Declaration -> Bool
ambiguousClauseTouches old name decl = case decl.value of
  NEquationLambda _ [argument] _ (NDataCase _ _ Nothing arms) =>
    argument.spelling == "$clauseScrutinee" &&
    case reverse arms of
      (head, [], _) :: _ => head.spelling == old || head.spelling == name
      _ => False
  _ => False

ambiguousItemTouches : String -> String -> AuthoredDeclaration -> Bool
ambiguousItemTouches old name (Ordinary decl) = ambiguousClauseTouches old name decl
ambiguousItemTouches old name (ImplementationItem decl) = ambiguousClauseTouches old name decl
ambiguousItemTouches old name (MutualItem group) = ambiguousClauseTouches old name group.first || ambiguousClauseTouches old name group.second
ambiguousItemTouches _ _ _ = False

||| Validate a new ASCII identifier, propose all declaration/use edits, and reject
||| any change in lexical resolution (including newly captured unresolved names).
||| No type-checking, cross-file safety, or source mutation is claimed.
public export
previewRename : String -> Nat -> Nat -> String -> Either RenameError RenamePreview
previewRename source line column name = do
  if validName name then Right () else Left InvalidRenameName
  let originalBytes = byteCount source
  if originalBytes <= 65536 then Right () else Left RenameSizeLimit
  document <- case parseDocument 64 256 source of
    Left err => Left (RenameFrontend err)
    Right document => Right document
  case (document.moduleHeader, document.imports) of
    (Nothing, []) => Right ()
    _ => Left RenameModuleUnsupported
  originalRefs <- the (Either RenameError (List Reference)) $ case documentReferences source of
    Left err => Left (RenameFrontend err)
    Right references => Right references
  selected <- case find (atCursor line column) originalRefs of
    Nothing => Left NoRenameTarget
    Just reference => Right reference
  old <- case find (\token => sameSpan token.span selected.origin) document.tokens of
    Nothing => Left RenameChangesScope
    Just token => Right token.spelling
  -- A different spelling cannot change whether an ambiguous head resolves to
  -- a global or bind its suppressed same-spelled uses. The usual reference
  -- comparison below still checks capture for every visible occurrence.
  case document.body of
    DeclarationDocument items => if any (ambiguousItemTouches old name) items then Left RenameChangesScope else Right ()
    _ => Right ()
  symbols <- case documentSymbols source of
    Left err => Left (RenameFrontend err)
    Right symbols => Right symbols
  if any (\symbol => sameSpan symbol.definitionSelection selected.target &&
                     (symbol.name == "main" || name == "main")) symbols
     then Left RenameEntrypoint else Right ()
  let edits = sortBy sourceOrder (map origin
                (filter (\reference => sameSpan reference.target selected.target) originalRefs))
  -- Edited names are ASCII: scalar widths equal byte widths for these spans.
  let removed = foldl (\count, span => count + minus span.finish.offset span.start.offset) 0 edits
  let candidateBytes = minus originalBytes removed + length edits * length (unpack name)
  if candidateBytes <= 65536 then Right () else Left RenameSizeLimit
  let candidate = pack (replaceFrom 0 (unpack source) (unpack name) edits)
  updatedRefs <- the (Either RenameError (List Reference)) $ case documentReferences candidate of
    Left _ => Left RenameChangesScope
    Right references => Right references
  if length originalRefs == length updatedRefs && all (preserved (length (unpack name)) edits updatedRefs) originalRefs
     then Right (Preview name (if candidate == source then [] else edits))
     else Left RenameChangesScope
