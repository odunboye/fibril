||| Isolated experimental source dialect; never calls production conversion.
module Fibril.Cubical.Source.Frontend

import Data.Fin
import Data.List
import Data.Vect
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.File
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.CommonAdmission
import Fibril.Foundation.DeMorgan.Scope
import Fibril.Foundation.DeMorgan.Interval

%default total

data Form = Atom Token | Group Position (List Form)

location : Form -> Position
location (Atom t) = t.span.start
location (Group p _) = p

failure : Form -> String -> Either String a
failure form message = Left (show (location form) ++ ": " ++ message)

mutual
  readForm : Nat -> Position -> List Token -> Either String (Form, List Token)
  readForm Z end ts = Left (show end ++ ": source form limit exhausted")
  readForm (S fuel) end [] = Left (show end ++ ": expected source form")
  readForm (S fuel) end (t :: ts) = case t.kind of
    OpenParen => do
      (forms, rest) <- readGroup fuel end ts
      Right (Group t.span.start forms, rest)
    CloseParen => Left (show t.span.start ++ ": unexpected closing parenthesis")
    _ => Right (Atom t, ts)

  readGroup : Nat -> Position -> List Token -> Either String (List Form, List Token)
  readGroup Z end ts = Left (show end ++ ": source form limit exhausted")
  readGroup (S fuel) end [] = Left (show end ++ ": missing closing parenthesis")
  readGroup (S fuel) end ts@(t :: rest) = case t.kind of
    CloseParen => Right ([], rest)
    _ => do
      (form, rest) <- readForm fuel end ts
      (forms, rest) <- readGroup fuel end rest
      Right (form :: forms, rest)

identifier : Form -> Either String String
identifier (Atom t) = if t.kind == Name && t.spelling /= "unit" then Right t.spelling
  else failure (Atom t) "expected non-keyword identifier (unit is reserved)"
identifier form = failure form "expected identifier"

lookupName : String -> Form -> Vect n String -> Either String (Fin n)
lookupName scope form names = do
  name <- identifier form
  find name names
  where
    find : String -> Vect m String -> Either String (Fin m)
    find name [] = failure form ("unknown " ++ scope ++ " name: " ++ name)
    find name (x :: xs) = if name == x then Right FZ else FS <$> find name xs

logicalType : Nat -> Form -> Either String LogicalType
logicalType Z f = failure f "type depth exhausted"
logicalType (S fuel) (Atom t) = case t.spelling of
  "Bool" => Right LBool
  "Unit" => Right LUnit
  _ => failure (Atom t) "unsupported type"
logicalType (S fuel) f@(Group _ [Atom op, a, b]) =
  if op.spelling == "arrow" then LArrow <$> logicalType fuel a <*> logicalType fuel b
  else failure f "expected (arrow TYPE TYPE)"
logicalType (S fuel) f = failure f "unsupported type form"

ordinary : Nat -> Vect n String -> Form -> Either String (AdmissionTerm n)
ordinary Z names f = failure f "term depth exhausted"
ordinary (S fuel) names (Atom t) = case t.spelling of
  "unit" => Right AUnit
  "True" => Right (ABool True)
  "False" => Right (ABool False)
  _ => AVar <$> lookupName "ordinary" (Atom t) names
ordinary (S fuel) names f@(Group _ [Atom op, binder, body]) = case op.spelling of
  "lam" => do
    name <- identifier binder
    ALam <$> ordinary fuel (name :: names) body
  "unitelim" => AUnitElim <$> ordinary fuel names binder <*> ordinary fuel names body
  _ => failure f "unsupported ordinary form"
ordinary (S fuel) names f@(Group _ [Atom op, a, b, c]) = case op.spelling of
  "app" => AApp <$> logicalType fuel a <*> ordinary fuel names b <*> ordinary fuel names c
  "if" => AIf <$> ordinary fuel names a <*> ordinary fuel names b <*> ordinary fuel names c
  _ => failure f "unsupported ordinary form"
ordinary (S fuel) names f = failure f "unsupported ordinary form"

side : Form -> Either String Bool
side f@(Atom t) = case t.spelling of
  "0" => Right False
  "1" => Right True
  _ => failure f "expected endpoint 0 or 1"
side f = failure f "expected endpoint 0 or 1"

interval : Nat -> Vect d String -> Form -> Either String (ScopedInterval d)
interval Z dims f = failure f "interval depth exhausted"
interval (S fuel) dims f@(Atom t) = case t.spelling of
  "0" => Right Zero
  "1" => Right One
  _ => Var <$> lookupName "dimension" f dims
interval (S fuel) dims f@(Group _ [Atom op, a]) =
  if op.spelling == "rev" then Reverse <$> interval fuel dims a
  else failure f "unsupported interval form"
interval (S fuel) dims f@(Group _ [Atom op, a, b]) = case op.spelling of
  "meet" => Meet <$> interval fuel dims a <*> interval fuel dims b
  "join" => Join <$> interval fuel dims a <*> interval fuel dims b
  _ => failure f "unsupported interval form"
interval (S fuel) dims f = failure f "unsupported interval form"

face : Nat -> Vect d String -> Form -> Either String (ScopedFace d)
face Z dims f = failure f "face depth exhausted"
face (S fuel) dims f@(Atom t) = case t.spelling of
  "top" => Right STop
  "bottom" => Right SBottom
  _ => failure f "unsupported face"
face (S fuel) dims f@(Group _ [Atom op, a, b]) = case op.spelling of
  "end" => SEndpoint <$> lookupName "dimension" a dims <*> side b
  "and" => SConjunction <$> face fuel dims a <*> face fuel dims b
  "or" => SDisjunction <$> face fuel dims a <*> face fuel dims b
  _ => failure f "unsupported face form"
face (S fuel) dims f = failure f "unsupported face form"

pathTerm : Nat -> Vect n String -> Vect k String -> Vect d String -> Form ->
  Either String (AdmissionPathTerm n k d)
pathTerm Z names paths dims f = failure f "path term depth exhausted"
pathTerm (S fuel) names paths dims f@(Group _ [Atom op, a]) =
  if op.spelling == "ordinary" then APOrdinary <$> ordinary fuel names a
  else failure f "unsupported path term form"
pathTerm (S fuel) names paths dims f@(Group _ [Atom op, a, b]) = case op.spelling of
  "at" => APAt <$> lookupName "path" a paths <*> interval fuel dims b
  "lam" => do
    name <- identifier a
    APLam <$> pathTerm fuel (name :: names) paths dims b
  "unitelim" => APUnitElim <$> pathTerm fuel names paths dims a <*> pathTerm fuel names paths dims b
  _ => failure f "unsupported path term form"
pathTerm (S fuel) names paths dims f@(Group _ [Atom op, a, b, c]) = case op.spelling of
  "app" => APApp <$> logicalType fuel a <*> pathTerm fuel names paths dims b <*> pathTerm fuel names paths dims c
  "if" => APIf <$> pathTerm fuel names paths dims a <*> pathTerm fuel names paths dims b <*> pathTerm fuel names paths dims c
  _ => failure f "unsupported path term form"
pathTerm (S fuel) names paths dims f = failure f "expected explicit path term form"

certificate : Nat -> Vect n String -> Vect k String -> Vect d String -> Form ->
  Either String (AdmissionEquality n k d)
certificate Z names paths dims f = failure f "certificate depth exhausted"
certificate (S fuel) names paths dims f@(Atom t) =
  if t.spelling == "refl" then Right AERefl else failure f "unsupported certificate"
certificate (S fuel) names paths dims f@(Group _ [Atom op, a]) =
  if op.spelling == "sym" then AESym <$> certificate fuel names paths dims a
  else failure f "unsupported certificate form"
certificate (S fuel) names paths dims f@(Group _ [Atom op, a, b]) = case op.spelling of
  "restrict" => AERestrict <$> face fuel dims a <*> certificate fuel names paths dims b
  "unitelim" => AEUnitElim <$> certificate fuel names paths dims a <*> certificate fuel names paths dims b
  _ => failure f "unsupported certificate form"
certificate (S fuel) names paths dims f@(Group _ [Atom op, a, b, c]) = case op.spelling of
  "endpoint" => AEEndpoint <$> lookupName "path" a paths <*> interval fuel dims b <*> side c
  "trans" => AETrans <$> pathTerm fuel names paths dims a <*> certificate fuel names paths dims b <*> certificate fuel names paths dims c
  "app" => AEApp <$> logicalType fuel a <*> certificate fuel names paths dims b <*> certificate fuel names paths dims c
  "if" => AEIf <$> certificate fuel names paths dims a <*> certificate fuel names paths dims b <*> certificate fuel names paths dims c
  _ => failure f "unsupported certificate form"
certificate (S fuel) names paths dims f = failure f "unsupported certificate form"

record Context where
  constructor MkContext
  size : Nat
  names : Vect size String
  types : Vect size LogicalType

context : List Form -> Either String Context
context [] = Right (MkContext 0 [] [])
context (f@(Group _ [binder, ty]) :: rest) = do
  name <- identifier binder
  a <- logicalType 64 ty
  MkContext n names types <- context rest
  if elem name names then failure binder "duplicate ordinary declaration" else
    Right (MkContext (S n) (name :: names) (a :: types))
context (f :: _) = failure f "expected (NAME TYPE) context entry"

record Paths (n : Nat) where
  constructor MkPaths
  size : Nat
  names : Vect size String
  declarations : AdmissionDeclarations n size

pathDeclarations : Vect n String -> List Form -> Either String (Paths n)
pathDeclarations names [] = Right (MkPaths 0 [] ADNil)
pathDeclarations names (f@(Group _ [binder, ty, left, right]) :: rest) = do
  name <- identifier binder
  a <- logicalType 64 ty
  l <- ordinary 64 names left
  r <- ordinary 64 names right
  MkPaths k paths declarations <- pathDeclarations names rest
  if elem name paths then failure binder "duplicate path declaration" else
    Right (MkPaths (S k) (name :: paths) (ADCons a l r declarations))
pathDeclarations names (f :: _) = failure f "expected (NAME TYPE ORDINARY ORDINARY) path declaration"

dimensions : List Form -> Either String (d ** Vect d String)
dimensions [] = Right (0 ** [])
dimensions (f :: rest) = do
  name <- identifier f
  (d ** dims) <- dimensions rest
  if elem name dims then failure f "duplicate dimension declaration" else Right (S d ** name :: dims)

allowance : Form -> Either String Nat
allowance f@(Atom t) =
  let chars = unpack t.spelling in
  if t.kind == Number && length chars <= 4
     then let value : Nat = foldl (\n, c => n * 10 + cast (ord c - ord '0')) 0 chars in
       if value <= 4096 then Right value else failure f "budget must be 0..4096"
     else failure f "budget must be decimal 0..4096"
allowance f = failure f "expected decimal budget"

admissionError : AdmissionError -> String
admissionError InputLimit = "InputLimit"
admissionError CheckingLimit = "CheckingLimit"
admissionError TypeMismatch = "TypeMismatch"
admissionError SyntaxMismatch = "SyntaxMismatch"
admissionError UnsupportedEquality = "UnsupportedEquality"
admissionError SolverLimit = "SolverLimit"
admissionError FaceMismatch = "FaceMismatch (false, inconclusive or capped entailment)"

checkForm : Form -> Either String (List String)
checkForm f@(Group _ [Atom header,
    Group _ [Atom budgetTag, input, checking, calls],
    Group _ (Atom contextTag :: entries),
    Group _ (Atom pathsTag :: declarations),
    Group _ (Atom dimsTag :: dims),
    abstraction@(Group _ [Atom abstractTag, binder, ty, ambient, left, right,
      Group _ [Atom lambdaTag, dim, body], zero, one])]) = do
  if header.spelling == "cubical" && budgetTag.spelling == "budget" &&
     contextTag.spelling == "context" && pathsTag.spelling == "paths" &&
     dimsTag.spelling == "dimensions" && abstractTag.spelling == "abstract" &&
     lambdaTag.spelling == "lambda" then Right () else failure f "invalid cubical file framing"
  i <- allowance input
  c <- allowance checking
  s <- allowance calls
  MkContext n names types <- context entries
  MkPaths k paths raw <- pathDeclarations names declarations
  (d ** dimensions) <- dimensions dims
  name <- identifier binder
  a <- logicalType 64 ty
  phi <- face 64 dimensions ambient
  l <- pathTerm 64 names paths dimensions left
  r <- pathTerm 64 names paths dimensions right
  fresh <- identifier dim
  let extended = fresh :: dimensions
  b <- pathTerm 64 names paths extended body
  z <- certificate 64 names paths extended zero
  o <- certificate 64 names paths extended one
  case admitCanonicalCommonAbstraction (MkCanonicalEqualityBudget (MkAdmissionBudget i c) s)
      types raw phi l r b a z o of
    Left err => failure abstraction ("cubical admission: " ++ admissionError err)
    Right admitted => Right
      ["Checked experimental cubical abstraction " ++ name ++ " (zero and one boundaries).",
       "Semantic provider conditional on CanonicalPathAdmissible for the checked declarations; no model existence or runtime execution claimed."]
checkForm f = failure f "expected (cubical (budget ...) (context ...) (paths ...) (dimensions ...) (abstract ...))"

public export
checkCubicalSource : String -> Either String (List String)
checkCubicalSource source = do
  tokens <- case lexSource source of
    Left err => Left (show err)
    Right tokens => Right tokens
  if length tokens > 4096 then Left "cubical source token limit (4096) exceeded" else Right ()
  let end = advancePosition (At 0 1 1) (unpack source)
  (form, rest) <- readForm 512 end tokens
  case rest of
    [] => checkForm form
    t :: _ => Left (show t.span.start ++ ": unexpected trailing source")

public export
checkCubicalFile : String -> IO (Either String (List String))
checkCubicalFile path = do
  loaded <- loadSourceWithin 16384 path
  pure $ case loaded of
    Left err => Left (path ++ ": " ++ show err)
    Right source => case checkCubicalSource source of
      Left err => Left (path ++ ":" ++ err)
      Right report => Right report
