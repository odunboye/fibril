-- Scoped quantitative dependent syntax, including internal finite variants; not a type checker.
-- See docs/core-draft.md; cubical resource rules remain unresolved.
-- Theory: DEBRUIJN72 (nameless indices); ATKEY18 sec. 2 (QTT background, not implemented typing).
-- Bibliography and limitations: docs/references.md.
module Fibril.Core.Term

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Data.Bytes

%default total

||| Terms in a context of n computational variables; 0 is newest.
||| Binder annotations are syntax, not evidence that usage has been checked.
public export
data Term : Nat -> Type where
  Variable : Fin n -> Term n
  Universe : Nat -> Term n
  ||| Primitive Unit : Type0; explicit case elimination, no eta rule (docs/unit.md).
  UnitType : Term n
  ||| Closed constructor () : Unit; zero runtime usage, not linear discard.
  UnitValue : Term n
  ||| Primitive Bool : Type0; distinct from cubical dimensions (docs/boolean.md).
  BoolType : Term n
  BoolTrue : Term n
  BoolFalse : Term n
  ||| Built-in natural numbers and structural dependent recursion.
  NatType : Term n
  NatZero : Term n
  NatSucc : Term n -> Term n
  NatRec : Term n -> Term n -> Term n -> Term n -> Term n
  ||| Structural recursion with a runtime predecessor and unrestricted count.
  NatRecRuntime : Term n -> Term n -> Term n -> Term n -> Term n
  ||| Closed fixed-shape recursive data: a terminal and one linear self field.
  ||| The key distinguishes families; the complete two-arm shape is intrinsic.
  RecType : String -> Term n
  RecEnd : Term n -> Term n
  RecMore : Term n -> Term n -> Term n
  RecFold : Term n -> Term n -> Term n -> Term n -> Term n
  ||| Non-recursive elimination exposes a linear tail without an induction result.
  RecCase : Term n -> Term n -> Term n -> Term n -> Term n
  ||| Fixed positive list shape: one terminal and one linear element/tail arm.
  SeqType : String -> Term n -> Term n
  SeqNil : Term n -> Term n
  SeqCons : Term n -> Term n -> Term n -> Term n
  SeqFold : Term n -> Term n -> Term n -> Term n -> Term n
  ||| One-step list matching exposes linear head and tail without recursion.
  SeqCase : Term n -> Term n -> Term n -> Term n -> Term n
  ||| Pure immutable octets, separate from text and from binary execution.
  BytesType : Term n
  BytesValue : Bytes -> Term n
  BytesAppend : Term n -> Term n -> Term n
  BytesLength : Term n -> Term n
  BytesIndex : Term n -> Term n -> Term n
  BytesSlice : Term n -> Term n -> Term n -> Term n
  ||| Low eight bits of a canonical natural, explicitly modulo 256.
  BytesOctet : Term n -> Term n
  ||| Primitive String : Type0, literal data, pure concatenation/comparison.
  StringType : Term n
  StringValue : String -> Term n
  StringAppend : Term n -> Term n -> Term n
  StringEqual : Term n -> Term n -> Term n
  ||| Closed nominal identity retains parameters (including phantom ones) and a checked variant shape.
  NominalType : String -> List (Term n) -> Term n -> Term n
  ||| Annotated wrapper value; underlying variant is independently checked.
  NominalValue : Term n -> Term n -> Term n
  ||| Erased dependent motive and a branch consuming the underlying variant once.
  NominalCase : Term n -> Term n -> Term n -> Term n
  ||| Internal finite variants; empty shapes and malformed tags are rejected by checking.
  VariantType : List (Maybe (Quantity, Term n)) -> Term n
  ||| Annotated positional constructor: nullary has Nothing, payload has Just value.
  VariantValue : Term n -> Nat -> Maybe (Term n) -> Term n
  ||| Explicit erased dependent motive, scrutinee and exhaustive positional branches.
  VariantCase : Term n -> Term n -> List (Term n) -> Term n
  BoxType : Quantity -> Term n -> Term n
  BoxValue : Term n -> Term n -> Term n
  BoxCase : Term n -> Term n -> Term n -> Term n
  ||| Pure descriptions of effects; only the external runner performs writes.
  IOType : Term n -> Term n
  ||| Opaque file ownership indexed by an erased small region type. No value constructor.
  FileHandleType : Term n -> Term n
  ||| Trusted runtime reference only; no source constructor or raw file pointer.
  FileHandleValue : Nat -> Nat -> Term n
  ||| Consume ownership and return its successor alongside a line/EOF/error result.
  ReadInputFile : Term n -> Term n
  ||| Inert scope: result type, path and region-polymorphic ownership-returning body.
  WithInputFile : Term n -> Term n -> Term n -> Term n
  IOPure : Term n -> Term n
  IOBind : Term n -> Term n -> Term n -> Term n -> Term n
  WriteLine : Term n -> Term n
  ||| Inert input request. EOF/line/error are positional alternatives in readResultType.
  ReadLine : Term n
  ||| Nondependent branches; runtime checking joins their resource permissions.
  BoolCase : Term n -> Term n -> Term n -> Term n
  Sigma : Quantity -> Quantity -> Term n -> Term (S n) -> Term n
  PairValue : Term n -> Term n -> Term n -> Term n
  PairCase : Term n -> Term n -> Term n -> Term n
  Pi : Quantity -> Term n -> Term (S n) -> Term n
  Lambda : Quantity -> Term n -> Term (S n) -> Term n
  Apply : Term n -> Term n -> Term n
  ||| Consume a Unit scrutinee, then return a body with no new pattern binders.
  UnitCase : Term n -> Term n -> Term n

||| Canonical unary natural; construction itself performs no external effect.
public export
naturalTerm : Nat -> Term n
naturalTerm Z = NatZero
naturalTerm (S n) = NatSucc (naturalTerm n)

public export
canonicalNatural : Term n -> Maybe Nat
canonicalNatural NatZero = Just Z
canonicalNatural (NatSucc n) = map S (canonicalNatural n)
canonicalNatural _ = Nothing

||| Missing or found octet (as a natural 0..255), never a sentinel byte.
public export
byteIndexResultType : Term n
byteIndexResultType = VariantType [Nothing, Just (Linear, NatType)]

public export
indexBytesValue : Nat -> Bytes -> Term n
indexBytesValue index bytes = case byteAt index bytes of
  Nothing => VariantValue byteIndexResultType 0 Nothing
  Just octet => VariantValue byteIndexResultType 1 (Just (naturalTerm (cast octet)))

public export
contractBytesIndex : Term n -> Term n -> Maybe (Term n)
contractBytesIndex index (BytesValue bytes) = map (\n => indexBytesValue n bytes) (canonicalNatural index)
contractBytesIndex _ _ = Nothing

public export
contractBytesSlice : Term n -> Term n -> Term n -> Maybe (Term n)
contractBytesSlice start count (BytesValue bytes) = do
  offset <- canonicalNatural start
  capacity <- canonicalNatural count
  Just (BytesValue (slice offset capacity bytes))
contractBytesSlice _ _ _ = Nothing

||| Only canonical naturals contract; Bits8 addition deliberately wraps.
public export
canonicalOctet : Term n -> Maybe Bits8
canonicalOctet NatZero = Just 0
canonicalOctet (NatSucc n) = map (+ 1) (canonicalOctet n)
canonicalOctet _ = Nothing

||| Total list selection for raw constructor tags; out-of-range is not an exception.
public export
variantAt : Nat -> List a -> Maybe a
variantAt _ [] = Nothing
variantAt Z (x :: _) = Just x
variantAt (S tag) (_ :: rest) = variantAt tag rest

||| Internal input result: tag 0 EOF, tag 1 line, tag 2 represented error.
||| String payloads must be consumed linearly; no host execution happens here.
public export
readResultType : Term n
readResultType = VariantType [Nothing, Just (Linear, StringType), Just (Linear, StringType)]

||| Internal nominal region identity, fresh within one resource-runner session.
||| The reserved key cannot be named by source identifiers; raw core remains trusted.
public export
runtimeFileRegion : Nat -> Term n
runtimeFileRegion identity = NominalType ("$fibril.file-region." ++ show identity) [] (VariantType [Nothing])

||| A successful read operation always returns ownership, including EOF/read errors.
public export
fileReadResultType : Term n -> Term n
fileReadResultType region = Sigma Linear Linear (FileHandleType region) readResultType

||| Scope result: open failure, success, or result plus cleanup failure.
public export
fileScopeResultType : Term n -> Term n
fileScopeResultType result = VariantType
  [Just (Linear, StringType), Just (Linear, result),
   Just (Linear, Sigma Linear Linear result StringType)]

mutual
  ||| Extend a renaming under one binder, preserving the newly bound variable.
  public export
  liftRenaming : (Fin n -> Fin m) -> Fin (S n) -> Fin (S m)
  liftRenaming env FZ = FZ
  liftRenaming env (FS i) = FS (env i)

  ||| Rename free variables; domain annotations remain outside the binder scope.
  public export
  rename : (Fin n -> Fin m) -> Term n -> Term m
  rename env (Variable i) = Variable (env i)
  rename env (Universe l) = Universe l
  rename env UnitType = UnitType
  rename env UnitValue = UnitValue
  rename env BoolType = BoolType
  rename env BoolTrue = BoolTrue
  rename env BoolFalse = BoolFalse
  rename env NatType = NatType
  rename env NatZero = NatZero
  rename env (NatSucc value) = NatSucc (rename env value)
  rename env (NatRec motive base step value) = NatRec (rename env motive) (rename env base) (rename env step) (rename env value)
  rename env (NatRecRuntime motive base step value) = NatRecRuntime (rename env motive) (rename env base) (rename env step) (rename env value)
  rename env (RecType key) = RecType key
  rename env (RecEnd ty) = RecEnd (rename env ty)
  rename env (RecMore ty value) = RecMore (rename env ty) (rename env value)
  rename env (RecFold motive base step value) = RecFold (rename env motive) (rename env base) (rename env step) (rename env value)
  rename env (RecCase motive value base more) = RecCase (rename env motive) (rename env value) (rename env base) (rename env more)
  rename env (SeqType key element) = SeqType key (rename env element)
  rename env (SeqNil ty) = SeqNil (rename env ty)
  rename env (SeqCons ty head tail) = SeqCons (rename env ty) (rename env head) (rename env tail)
  rename env (SeqFold motive base step value) = SeqFold (rename env motive) (rename env base) (rename env step) (rename env value)
  rename env (SeqCase motive value base cons) = SeqCase (rename env motive) (rename env value) (rename env base) (rename env cons)
  rename env ReadLine = ReadLine
  rename env (FileHandleValue identity generation) = FileHandleValue identity generation
  rename env (ReadInputFile handle) = ReadInputFile (rename env handle)
  rename env BytesType = BytesType
  rename env (BytesValue value) = BytesValue value
  rename env (BytesAppend a b) = BytesAppend (rename env a) (rename env b)
  rename env (BytesIndex a b) = BytesIndex (rename env a) (rename env b)
  rename env (BytesSlice a b c) = BytesSlice (rename env a) (rename env b) (rename env c)
  rename env (BytesLength a) = BytesLength (rename env a)
  rename env (BytesOctet a) = BytesOctet (rename env a)
  rename env StringType = StringType
  rename env (StringValue value) = StringValue value
  rename env (StringAppend left right) = StringAppend (rename env left) (rename env right)
  rename env (BoxValue left right) = BoxValue (rename env left) (rename env right)
  rename env (StringEqual left right) = StringEqual (rename env left) (rename env right)
  rename env (IOType ty) = IOType (rename env ty)
  rename env (WithInputFile result path body) = WithInputFile (rename env result) (rename env path) (rename env body)
  rename env (FileHandleType region) = FileHandleType (rename env region)
  rename env (NominalType key indices shape) = NominalType key (renameTerms env indices) (rename env shape)
  rename env (NominalValue ty value) = NominalValue (rename env ty) (rename env value)
  rename env (NominalCase motive value branch) = NominalCase (rename env motive) (rename env value) (rename env branch)
  rename env (VariantType arms) = VariantType (renameArms env arms)
  rename env (VariantValue ty tag Nothing) = VariantValue (rename env ty) tag Nothing
  rename env (VariantValue ty tag (Just value)) = VariantValue (rename env ty) tag (Just (rename env value))
  rename env (VariantCase motive value branches) = VariantCase (rename env motive) (rename env value) (renameTerms env branches)
  rename env (BoxType q ty) = BoxType q (rename env ty)
  rename env (IOPure value) = IOPure (rename env value)
  rename env (WriteLine text) = WriteLine (rename env text)
  rename env (IOBind a b action next) =
    IOBind (rename env a) (rename env b) (rename env action) (rename env next)
  rename env (BoolCase condition yes no) =
    BoolCase (rename env condition) (rename env yes) (rename env no)
  rename env (PairCase motive scrutinee branch) =
    PairCase (rename env motive) (rename env scrutinee) (rename env branch)
  rename env (BoxCase motive scrutinee branch) =
    BoxCase (rename env motive) (rename env scrutinee) (rename env branch)
  rename env (PairValue annotation firstValue secondValue) =
    PairValue (rename env annotation) (rename env firstValue) (rename env secondValue)
  rename env (Pi q domain body) =
    Pi q (rename env domain) (rename (liftRenaming env) body)
  rename env (Sigma q r domain body) =
    Sigma q r (rename env domain) (rename (liftRenaming env) body)
  rename env (Lambda q domain body) =
    Lambda q (rename env domain) (rename (liftRenaming env) body)
  rename env (Apply f x) = Apply (rename env f) (rename env x)
  rename env (UnitCase scrutinee body) = UnitCase (rename env scrutinee) (rename env body)

  ||| Insert a newest variable, shifting all existing free references.
  public export
  weaken : Term n -> Term (S n)
  weaken = rename FS

  ||| Extend substitution under a binder, weakening replacements to avoid capture.
  public export
  liftSubstitution : (Fin n -> Term m) -> Fin (S n) -> Term (S m)
  liftSubstitution env FZ = Variable FZ
  liftSubstitution env (FS i) = weaken (env i)

  ||| Simultaneous capture-avoiding substitution; performs no reduction.
  public export
  substituteTerm : (Fin n -> Term m) -> Term n -> Term m
  substituteTerm env (Variable i) = env i
  substituteTerm env (Universe l) = Universe l
  substituteTerm env UnitType = UnitType
  substituteTerm env UnitValue = UnitValue
  substituteTerm env BoolType = BoolType
  substituteTerm env BoolTrue = BoolTrue
  substituteTerm env BoolFalse = BoolFalse
  substituteTerm env NatType = NatType
  substituteTerm env NatZero = NatZero
  substituteTerm env (NatSucc value) = NatSucc (substituteTerm env value)
  substituteTerm env (NatRec motive base step value) = NatRec (substituteTerm env motive) (substituteTerm env base) (substituteTerm env step) (substituteTerm env value)
  substituteTerm env (NatRecRuntime motive base step value) = NatRecRuntime (substituteTerm env motive) (substituteTerm env base) (substituteTerm env step) (substituteTerm env value)
  substituteTerm env (RecType key) = RecType key
  substituteTerm env (RecEnd ty) = RecEnd (substituteTerm env ty)
  substituteTerm env (RecMore ty value) = RecMore (substituteTerm env ty) (substituteTerm env value)
  substituteTerm env (RecFold motive base step value) = RecFold (substituteTerm env motive) (substituteTerm env base) (substituteTerm env step) (substituteTerm env value)
  substituteTerm env (RecCase motive value base more) = RecCase (substituteTerm env motive) (substituteTerm env value) (substituteTerm env base) (substituteTerm env more)
  substituteTerm env (SeqType key element) = SeqType key (substituteTerm env element)
  substituteTerm env (SeqNil ty) = SeqNil (substituteTerm env ty)
  substituteTerm env (SeqCons ty head tail) = SeqCons (substituteTerm env ty) (substituteTerm env head) (substituteTerm env tail)
  substituteTerm env (SeqFold motive base step value) = SeqFold (substituteTerm env motive) (substituteTerm env base) (substituteTerm env step) (substituteTerm env value)
  substituteTerm env (SeqCase motive value base cons) = SeqCase (substituteTerm env motive) (substituteTerm env value) (substituteTerm env base) (substituteTerm env cons)
  substituteTerm env ReadLine = ReadLine
  substituteTerm env (FileHandleValue identity generation) = FileHandleValue identity generation
  substituteTerm env (ReadInputFile handle) = ReadInputFile (substituteTerm env handle)
  substituteTerm env BytesType = BytesType
  substituteTerm env (BytesValue value) = BytesValue value
  substituteTerm env (BytesAppend a b) = BytesAppend (substituteTerm env a) (substituteTerm env b)
  substituteTerm env (BytesIndex a b) = BytesIndex (substituteTerm env a) (substituteTerm env b)
  substituteTerm env (BytesSlice a b c) = BytesSlice (substituteTerm env a) (substituteTerm env b) (substituteTerm env c)
  substituteTerm env (BytesLength a) = BytesLength (substituteTerm env a)
  substituteTerm env (BytesOctet a) = BytesOctet (substituteTerm env a)
  substituteTerm env StringType = StringType
  substituteTerm env (StringValue value) = StringValue value
  substituteTerm env (StringAppend left right) =
    StringAppend (substituteTerm env left) (substituteTerm env right)
  substituteTerm env (BoxValue left right) =
    BoxValue (substituteTerm env left) (substituteTerm env right)
  substituteTerm env (StringEqual left right) =
    StringEqual (substituteTerm env left) (substituteTerm env right)
  substituteTerm env (IOType ty) = IOType (substituteTerm env ty)
  substituteTerm env (WithInputFile result path body) = WithInputFile (substituteTerm env result) (substituteTerm env path) (substituteTerm env body)
  substituteTerm env (FileHandleType region) = FileHandleType (substituteTerm env region)
  substituteTerm env (NominalType key indices shape) = NominalType key (substituteTerms env indices) (substituteTerm env shape)
  substituteTerm env (NominalValue ty value) = NominalValue (substituteTerm env ty) (substituteTerm env value)
  substituteTerm env (NominalCase motive value branch) = NominalCase (substituteTerm env motive) (substituteTerm env value) (substituteTerm env branch)
  substituteTerm env (VariantType arms) = VariantType (substituteArms env arms)
  substituteTerm env (VariantValue ty tag Nothing) = VariantValue (substituteTerm env ty) tag Nothing
  substituteTerm env (VariantValue ty tag (Just value)) = VariantValue (substituteTerm env ty) tag (Just (substituteTerm env value))
  substituteTerm env (VariantCase motive value branches) = VariantCase (substituteTerm env motive) (substituteTerm env value) (substituteTerms env branches)
  substituteTerm env (BoxType q ty) = BoxType q (substituteTerm env ty)
  substituteTerm env (IOPure value) = IOPure (substituteTerm env value)
  substituteTerm env (WriteLine text) = WriteLine (substituteTerm env text)
  substituteTerm env (IOBind a b action next) =
    IOBind (substituteTerm env a) (substituteTerm env b)
           (substituteTerm env action) (substituteTerm env next)
  substituteTerm env (BoolCase condition yes no) =
    BoolCase (substituteTerm env condition) (substituteTerm env yes) (substituteTerm env no)
  substituteTerm env (PairCase motive scrutinee branch) =
    PairCase (substituteTerm env motive) (substituteTerm env scrutinee) (substituteTerm env branch)
  substituteTerm env (BoxCase motive scrutinee branch) =
    BoxCase (substituteTerm env motive) (substituteTerm env scrutinee) (substituteTerm env branch)
  substituteTerm env (PairValue annotation firstValue secondValue) =
    PairValue (substituteTerm env annotation) (substituteTerm env firstValue) (substituteTerm env secondValue)
  substituteTerm env (Pi q domain body) =
    Pi q (substituteTerm env domain) (substituteTerm (liftSubstitution env) body)
  substituteTerm env (Sigma q r domain body) =
    Sigma q r (substituteTerm env domain) (substituteTerm (liftSubstitution env) body)
  substituteTerm env (Lambda q domain body) =
    Lambda q (substituteTerm env domain) (substituteTerm (liftSubstitution env) body)
  substituteTerm env (Apply f x) = Apply (substituteTerm env f) (substituteTerm env x)
  substituteTerm env (UnitCase scrutinee body) =
    UnitCase (substituteTerm env scrutinee) (substituteTerm env body)

  ||| Replacement map for removing the newest variable from a scope.
  ||| Factored out so structural proofs use the exact same map as instantiation.
  public export
  replaceNewest : Term n -> Fin (S n) -> Term n
  replaceNewest value FZ = value
  replaceNewest value (FS i) = Variable i

  ||| Replace the newest free variable; older indices shift down.
  ||| This is a syntactic operation, not a checked beta-reduction rule.
  public export
  instantiateTerm : Term n -> Term (S n) -> Term n
  instantiateTerm value = substituteTerm (replaceNewest value)

  ||| Structural syntax equality only, not definitional equality or path equality.
  public export
  sameSyntax : Term n -> Term n -> Bool
  sameSyntax (Variable i) (Variable j) = i == j
  sameSyntax (Universe l) (Universe k) = l == k
  sameSyntax UnitType UnitType = True
  sameSyntax UnitValue UnitValue = True
  sameSyntax BoolType BoolType = True
  sameSyntax BoolTrue BoolTrue = True
  sameSyntax BoolFalse BoolFalse = True
  sameSyntax NatType NatType = True
  sameSyntax NatZero NatZero = True
  sameSyntax (NatSucc x) (NatSucc y) = sameSyntax x y
  sameSyntax (NatRec p z s x) (NatRec q w t y) = sameSyntax p q && sameSyntax z w && sameSyntax s t && sameSyntax x y
  sameSyntax (NatRecRuntime p z s x) (NatRecRuntime q w t y) = sameSyntax p q && sameSyntax z w && sameSyntax s t && sameSyntax x y
  sameSyntax (RecType x) (RecType y) = x == y
  sameSyntax (RecEnd x) (RecEnd y) = sameSyntax x y
  sameSyntax (RecMore t x) (RecMore u y) = sameSyntax t u && sameSyntax x y
  sameSyntax (RecFold p z s x) (RecFold q w t y) = sameSyntax p q && sameSyntax z w && sameSyntax s t && sameSyntax x y
  sameSyntax (RecCase p x z s) (RecCase q y w t) = sameSyntax p q && sameSyntax x y && sameSyntax z w && sameSyntax s t
  sameSyntax (SeqType key a) (SeqType other b) = key == other && sameSyntax a b
  sameSyntax (SeqNil a) (SeqNil b) = sameSyntax a b
  sameSyntax (SeqCons a h t) (SeqCons b x y) = sameSyntax a b && sameSyntax h x && sameSyntax t y
  sameSyntax (SeqFold p z s x) (SeqFold q w t y) = sameSyntax p q && sameSyntax z w && sameSyntax s t && sameSyntax x y
  sameSyntax (SeqCase p x z s) (SeqCase q y w t) = sameSyntax p q && sameSyntax x y && sameSyntax z w && sameSyntax s t
  sameSyntax ReadLine ReadLine = True
  sameSyntax (FileHandleValue left first) (FileHandleValue right second) = left == right && first == second
  sameSyntax (ReadInputFile left) (ReadInputFile right) = sameSyntax left right
  sameSyntax BytesType BytesType = True
  sameSyntax (BytesValue a) (BytesValue b) = a == b
  sameSyntax (BytesAppend a b) (BytesAppend c d) = sameSyntax a c && sameSyntax b d
  sameSyntax (BytesIndex a b) (BytesIndex c d) = sameSyntax a c && sameSyntax b d
  sameSyntax (BytesSlice a b c) (BytesSlice d e f) = sameSyntax a d && sameSyntax b e && sameSyntax c f
  sameSyntax (BytesLength a) (BytesLength b) = sameSyntax a b
  sameSyntax (BytesOctet a) (BytesOctet b) = sameSyntax a b
  sameSyntax StringType StringType = True
  sameSyntax (StringValue left) (StringValue right) = left == right
  sameSyntax (StringAppend a b) (StringAppend c d) = sameSyntax a c && sameSyntax b d
  sameSyntax (BoxValue a b) (BoxValue c d) = sameSyntax a c && sameSyntax b d
  sameSyntax (StringEqual a b) (StringEqual c d) = sameSyntax a c && sameSyntax b d
  sameSyntax (NominalType k xs a) (NominalType l ys b) = k == l && sameTerms xs ys && sameSyntax a b
  sameSyntax (NominalValue a x) (NominalValue b y) = sameSyntax a b && sameSyntax x y
  sameSyntax (NominalCase p x f) (NominalCase q y g) = sameSyntax p q && sameSyntax x y && sameSyntax f g
  sameSyntax (VariantType xs) (VariantType ys) = sameArms xs ys
  sameSyntax (VariantValue a i Nothing) (VariantValue b j Nothing) = i == j && sameSyntax a b
  sameSyntax (VariantValue a i (Just x)) (VariantValue b j (Just y)) = i == j && sameSyntax a b && sameSyntax x y
  sameSyntax (VariantCase p x fs) (VariantCase q y gs) = sameSyntax p q && sameSyntax x y && sameTerms fs gs
  sameSyntax (BoxType q a) (BoxType r b) = q == r && sameSyntax a b
  sameSyntax (IOType a) (IOType b) = sameSyntax a b
  sameSyntax (WithInputFile a p f) (WithInputFile b q g) = sameSyntax a b && sameSyntax p q && sameSyntax f g
  sameSyntax (FileHandleType a) (FileHandleType b) = sameSyntax a b
  sameSyntax (IOPure a) (IOPure b) = sameSyntax a b
  sameSyntax (WriteLine a) (WriteLine b) = sameSyntax a b
  sameSyntax (IOBind a b c d) (IOBind e f g h) =
    sameSyntax a e && sameSyntax b f && sameSyntax c g && sameSyntax d h
  sameSyntax (BoolCase c t e) (BoolCase d u f) =
    sameSyntax c d && sameSyntax t u && sameSyntax e f
  sameSyntax (Sigma q r a b) (Sigma s t c d) = q == s && r == t && sameSyntax a c && sameSyntax b d
  sameSyntax (PairCase p a f) (PairCase q b g) = sameSyntax p q && sameSyntax a b && sameSyntax f g
  sameSyntax (BoxCase p a f) (BoxCase q b g) = sameSyntax p q && sameSyntax a b && sameSyntax f g
  sameSyntax (PairValue ty a b) (PairValue expected c d) = sameSyntax ty expected && sameSyntax a c && sameSyntax b d
  sameSyntax (Pi q a b) (Pi r c d) = q == r && sameSyntax a c && sameSyntax b d
  sameSyntax (Lambda q a b) (Lambda r c d) = q == r && sameSyntax a c && sameSyntax b d
  sameSyntax (Apply f x) (Apply g y) = sameSyntax f g && sameSyntax x y
  sameSyntax (UnitCase u b) (UnitCase v c) = sameSyntax u v && sameSyntax b c
  sameSyntax _ _ = False

  public export
  renameArms : (env : Fin n -> Fin m) -> List (Maybe (Quantity, Term n)) -> List (Maybe (Quantity, Term m))
  renameArms env [] = []
  renameArms env (Nothing :: rest) = Nothing :: renameArms env rest
  renameArms env (Just (q, ty) :: rest) = Just (q, rename env ty) :: renameArms env rest

  public export
  renameTerms : (env : Fin n -> Fin m) -> List (Term n) -> List (Term m)
  renameTerms env [] = []
  renameTerms env (term :: rest) = rename env term :: renameTerms env rest

  public export
  substituteArms : (env : Fin n -> Term m) -> List (Maybe (Quantity, Term n)) -> List (Maybe (Quantity, Term m))
  substituteArms env [] = []
  substituteArms env (Nothing :: rest) = Nothing :: substituteArms env rest
  substituteArms env (Just (q, ty) :: rest) = Just (q, substituteTerm env ty) :: substituteArms env rest

  public export
  substituteTerms : (env : Fin n -> Term m) -> List (Term n) -> List (Term m)
  substituteTerms env [] = []
  substituteTerms env (term :: rest) = substituteTerm env term :: substituteTerms env rest

  public export
  sameArms : List (Maybe (Quantity, Term n)) -> List (Maybe (Quantity, Term n)) -> Bool
  sameArms [] [] = True
  sameArms (Nothing :: xs) (Nothing :: ys) = sameArms xs ys
  sameArms (Just (q, x) :: xs) (Just (r, y) :: ys) = q == r && sameSyntax x y && sameArms xs ys
  sameArms _ _ = False

  public export
  sameTerms : List (Term n) -> List (Term n) -> Bool
  sameTerms [] [] = True
  sameTerms (x :: xs) (y :: ys) = sameSyntax x y && sameTerms xs ys
  sameTerms _ _ = False

||| Branch signature for a checked finite-variant descriptor.
public export
variantBranchType : Term n -> Term n -> Nat -> Maybe (Quantity, Term n) -> Term n
variantBranchType motive ty tag Nothing = Apply motive (VariantValue ty tag Nothing)
variantBranchType motive ty tag (Just (q, domain)) =
  Pi q domain (Apply (weaken motive) (VariantValue (weaken ty) tag (Just (Variable FZ))))

||| Callback must return ownership under its abstract region, on every result path.
public export
scopedInputBodyType : Term n -> Term n
scopedInputBodyType result = Pi Erased (Universe 0)
  (Pi Linear (FileHandleType (Variable FZ))
    (IOType (Sigma Linear Linear (FileHandleType (Variable (FS FZ)))
      (weaken (weaken (weaken result))))))
