-- Strict local manifest decoding through pinned idris2-yaml, not a YAML parser.
-- No filesystem/path resolution, hooks, source checking or dependency fetching.
module Fibril.Project.Manifest

import Data.List
import Data.List1
import Data.String
import Text.YAML
import Fibril.Project.Name
import Fibril.Project.Workspace
import Fibril.Source.Text

%default total

public export
record PathDependency where
  constructor LocalPath
  name : String
  path : String

public export
record PackageManifest where
  constructor Manifest
  name : String
  modulePrefix : List String
  sourceDirectory : String
  foundation : String
  entry : Maybe String
  dependencies : List PathDependency

public export
record ManifestError where
  constructor InvalidManifest
  message : String

public export
Show ManifestError where
  show error = error.message

failure : String -> Either ManifestError a
failure = Left . InvalidManifest

utf8Bytes : String -> Nat
utf8Bytes text = foldl (\count, c => count + (if ord c < 128 then 1 else if ord c < 2048 then 2 else if ord c < 65536 then 3 else 4)) 0 (unpack text)

safeScalar : String -> Bool
safeScalar text = all (\c => ord c >= 32) (unpack text) && case validateText text of Right _ => True; _ => False

singleLine : Bounds -> Bool
singleLine (BS start end) = start.line == end.line
singleLine NoBounds = False

bare : Maybe Anchor -> Tag -> Bool
bare Nothing NoTag = True
bare _ _ = False

-- Event policy is checked before composition, so aliases are never expanded.
profile : Nat -> Nat -> List (Bounded Event) -> Either ManifestError ()
profile depth docs [] = if depth == 0 && docs == 1 then Right () else failure "Expected exactly one YAML document"
profile depth docs (B event bounds :: rest) = case event of
  StreamStart => profile depth docs rest
  StreamEnd => profile depth docs rest
  DocStart _ => if docs == 0 then profile depth 1 rest else failure "Multiple YAML documents are not supported"
  DocEnd _ => profile depth docs rest
  MapStart _ anchor tag => if depth < 3 && bare anchor tag then profile (S depth) docs rest
                          else failure "Manifest mappings exceed depth 3, or use anchors/tags"
  MapEnd => case depth of Z => failure "Unexpected YAML mapping end"; S remaining => profile remaining docs rest
  Scalar anchor tag style text =>
    if not (bare anchor tag) then failure "YAML anchors and explicit tags are not supported"
    else if elem style [Literal, Folded] || not (singleLine bounds) then failure "Manifest scalars must occupy one source line"
    else if length (unpack text) > 1024 || not (safeScalar text) then failure "Manifest scalar exceeds its limit or contains decoded control characters"
    else profile depth docs rest
  Alias _ => failure "YAML aliases are not supported"
  _ => failure "YAML sequences are not supported in package manifests"

mapping : String -> Node -> Either ManifestError (List (String, Node))
mapping field (NMap TMap pairs) = traverse key pairs
  where
    key : (Node, Node) -> Either ManifestError (String, Node)
    key (NScalar TStr _ text, value) = Right (text, value)
    key _ = failure (field ++ " requires string mapping keys")
mapping field _ = failure (field ++ " must be a mapping")

string : String -> Node -> Either ManifestError String
string field (NScalar TStr _ text) = Right text
string field _ = failure (field ++ " must be a string (quote ambiguous YAML scalars)")

required : String -> List (String, Node) -> Either ManifestError Node
required field entries = case lookup field entries of
  Nothing => failure ("Missing manifest field " ++ show field)
  Just value => Right value

unknown : List String -> List (String, Node) -> Either ManifestError ()
unknown allowed [] = Right ()
unknown allowed ((key, _) :: rest) = if elem key allowed then unknown allowed rest else failure ("Unknown manifest field " ++ show key)

||| Portable relative-path spelling only, not canonicalization or filesystem
||| authority. Dependency paths may traverse parents; source-dir may not.
public export
relativeManifestPath : Bool -> String -> Bool
relativeManifestPath parents text = case unpack text of
  [] => False
  '/' :: _ => False
  chars => safeScalar text && not (any (\c => c == '\\' || c == ':') chars) &&
    all (\part => part /= "" && (parents || (part /= "." && part /= ".."))) (forget (Data.String.split (== '/') text))

dependencies : String -> List (String, Node) -> Either ManifestError (List PathDependency)
dependencies owner fields = case lookup "dependencies" fields of
  Nothing => Right []
  Just node => do
    entries <- mapping "dependencies" node
    if length entries > 64 then failure "Manifest dependency admission exhausted (64)" else Right ()
    traverse entry entries
  where
    entry : (String, Node) -> Either ManifestError PathDependency
    entry (name, node) = do
      if not (validPackageName name) || name == owner then failure "Invalid or self dependency name" else Right ()
      fields <- mapping ("Dependency " ++ show name) node
      unknown ["path"] fields
      path <- required "path" fields >>= string "dependency path"
      if relativeManifestPath True path then Right (LocalPath name path) else failure "Dependency path must be an explicit safe relative path"

fromNode : Node -> Either ManifestError PackageManifest
fromNode node = do
  fields <- mapping "manifest" node
  unknown ["schema", "name", "module-prefix", "source-dir", "foundation", "entry", "dependencies"] fields
  schema <- required "schema" fields
  case schema of
    NScalar TInt Plain "1" => Right ()
    _ => failure "Manifest schema must be the plain decimal integer 1"
  name <- required "name" fields >>= string "name"
  if not (validPackageName name) then failure "Invalid package name" else Right ()
  owned <- required "module-prefix" fields >>= string "module-prefix"
  let parts = forget (Data.String.split (== '.') owned)
  if not (validModuleComponents parts) || (case parts of "Main" :: _ => True; _ => False)
     then failure "Invalid or reserved owned module prefix" else Right ()
  source <- required "source-dir" fields >>= string "source-dir"
  if not (relativeManifestPath False source) then failure "source-dir must be a relative path without empty/dot/parent components" else Right ()
  foundation <- required "foundation" fields >>= string "foundation"
  if foundation /= "de-morgan" then failure "Only de-morgan foundation metadata is currently supported" else Right ()
  entry <- case lookup "entry" fields of
    Nothing => Right Nothing
    Just value => do
      name <- string "entry" value
      if name == "Main" then Right (Just name) else failure "Only entry Main is currently supported"
  deps <- dependencies name fields
  Right (Manifest name parts source foundation entry deps)

||| Input admission precedes maintained parsing. Raw flow-delimiter/line limits
||| are conservative and count inside strings/comments too; they are not a YAML
||| lexer or wall-clock/stack/allocation guarantees. Schema errors are unlocated;
||| maintained-parser/composer errors retain their own real source bounds.
public export
decodeManifest : String -> String -> Either ManifestError PackageManifest
decodeManifest path source = do
  if utf8Bytes source > 8192 then failure "Manifest exceeds 8192 UTF-8 bytes" else Right ()
  case validateText source of
    Left error => failure (show error)
    Right _ => Right ()
  let rawLines = lines (normalized source)
  if length rawLines > 256 || length (filter (\c => elem c ['[', ']', '{', '}']) (unpack source)) > 128
     then failure "Manifest raw line/flow-delimiter admission exhausted" else Right ()
  if any (\line => case dropWhile (\c => c == ' ' || c == '\t') (unpack line) of '%' :: _ => True; _ => False) rawLines
     then failure "YAML directives are not supported" else Right ()
  events <- case parseEvents (FileSrc path) source of
    Left error => failure (interpolate error)
    Right events => Right events
  if length events > 512 then failure "Manifest event admission exhausted (512)" else Right ()
  profile 0 0 events
  docs <- case composeWith Core events of
    Left error => failure (interpolate (toParseError (FileSrc path) (normalized source) error))
    Right docs => Right docs
  case docs of
    [doc] => fromNode doc
    _ => failure "Expected exactly one YAML document"
