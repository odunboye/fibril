-- Checked core to C, independent of file/project loading and host execution.
module Fibril.Driver.Native.Emit

import Data.List
import Data.Fin
import Fibril.Core.Term
import Fibril.Core.EffectAdmission
import Fibril.Data.Bytes
import Fibril.Core.Quantity
import Fibril.Core.Context
import Fibril.Core.Runtime
import Fibril.Core.WeakHead
import Fibril.Core.ResourceAdmission
import Fibril.Core.Limits
import Fibril.Core.Size
import Fibril.Elaboration.Expression.Payload

%default total

data NativeMode = Preflight | Interactive | Resources | Binary

Eq NativeMode where
  Preflight == Preflight = True
  Interactive == Interactive = True
  Resources == Resources = True
  Binary == Binary = True
  _ == _ = False

record Generated where
  constructor Output
  root : Nat
  next : Nat
  definitions : List String

name : Nat -> String
name n = "fibril_expr_" ++ show n

prototype : Nat -> String
prototype n = "static FValue *" ++ name n ++ "(FRuntime *, FEnv *);\n"

function : Nat -> String -> String
function n body = "static FValue *" ++ name n ++ "(FRuntime *r, FEnv *e) { " ++ body ++ " }\n"

-- Emit decimal UTF-8 octets, never source-authored C tokens or C escapes.
utf8 : Char -> List Int
utf8 char =
  let x = ord char in
    if x < 128 then [x]
    else if x < 2048 then [192 + div x 64, 128 + mod x 64]
    else if x < 65536 then [224 + div x 4096, 128 + mod (div x 64) 64, 128 + mod x 64]
    else [240 + div x 262144, 128 + mod (div x 4096) 64, 128 + mod (div x 64) 64, 128 + mod x 64]

literal : Nat -> String -> String
literal n text =
  let bytes = concatMap utf8 (unpack text)
      contents = if null bytes then "0" else concat (intersperse "," (map show bytes)) in
    "static const unsigned char fibril_literal_" ++ show n ++ "[] = {" ++ contents ++ "};\n" ++
    function n ("(void)e; return f_literal(r, fibril_literal_" ++ show n ++ ", " ++ show (length bytes) ++ ");")

byteLiteral : Nat -> Bytes -> String
byteLiteral n value =
  let bytes : List Bits8 = Fibril.Data.Bytes.toList value
      contents = if null bytes then "0" else concat (intersperse "," (map show bytes)) in
    "static const unsigned char fibril_bytes_" ++ show n ++ "[] = {" ++ contents ++ "};\n" ++
    function n ("(void)e; return f_bytes_literal(r, fibril_bytes_" ++ show n ++ ", " ++ show (length bytes) ++ ");")

constant : Nat -> String -> Generated
constant n expr = Output n (S n) [function n ("(void)e; return " ++ expr ++ ";")]

mutual
  generate : NativeMode -> Nat -> Term n -> Either String Generated
  generate mode n (Variable index) = Right (Output n (S n) [function n ("return f_variable(r, e, " ++ show (finToNat index) ++ ");")])
  generate mode n (UTF8Encode x) = unary mode n "f_utf8_encode" x
  generate mode n (UTF8Decode x) = unary mode n "f_utf8_decode" x
  generate mode n BytesType = Right (constant n "f_erased(r)")
  generate mode n (BytesValue value) = Right (Output n (S n) [byteLiteral n value])
  generate mode n (BytesAppend a b) = binary mode n "f_bytes_append" a b
  generate mode n (BytesLengthIs a b) = binary mode n "f_bytes_length_is" a b
  generate mode n (BytesIndex a b) = binary mode n "f_bytes_index" a b
  generate mode n (BytesSlice a b c) = ternary mode n "f_bytes_slice" a b c
  generate mode n (BytesShare x) = unary mode n "f_nominal" x
  generate mode n (BytesLength x) = unary mode n "f_bytes_length" x
  generate mode n (BytesOctet x) = unary mode n "f_bytes_octet" x
  generate mode n (StringValue value) = Right (Output n (S n) [literal n value])
  generate mode n UnitValue = Right (constant n "f_unit(r)")
  generate mode n (Universe _) = Right (constant n "f_erased(r)")
  generate mode n UnitType = Right (constant n "f_erased(r)")
  generate mode n BoolType = Right (constant n "f_erased(r)")
  generate mode n NatType = Right (constant n "f_erased(r)")
  generate mode n (RecType _) = Right (constant n "f_erased(r)")
  generate mode n (SeqType _ _) = Right (constant n "f_erased(r)")
  generate mode n NatZero = Right (constant n "f_nat_zero(r)")
  generate mode n (NatSucc tail) = unary mode n "f_nat_succ" tail
  generate mode n (RecEnd _) = Right (constant n "f_rec_end(r)")
  generate mode n (RecMore _ tail) = unary mode n "f_rec_more" tail
  generate mode n (SeqNil _) = Right (constant n "f_seq_nil(r)")
  generate mode n (SeqCons _ head tail) = binary mode n "f_seq_cons" head tail
  generate mode n (NatRec _ base step value) = ternary mode n "f_nat_rec" base step value
  generate mode n (NatRecRuntime _ base step value) = ternary mode n "f_nat_rec_runtime" base step value
  generate mode n (RecFold _ base step value) = ternary mode n "f_rec_fold" base step value
  generate mode n (SeqFold _ base step value) = ternary mode n "f_seq_fold" base step value
  generate mode n (RecCase _ value base more) = ternary mode n "f_rec_case" value base more
  generate mode n (NatCase _ value base more) = ternary mode n "f_nat_case" value base more
  generate mode n (SeqCase _ value base cons) = ternary mode n "f_seq_case" value base cons
  generate mode n BoolTrue = Right (constant n "f_bool(r, 1)")
  generate mode n BoolFalse = Right (constant n "f_bool(r, 0)")
  generate mode n StringType = Right (constant n "f_erased(r)")
  generate mode n (IOType _) = Right (constant n "f_erased(r)")
  generate mode n (FileHandleType _) = Right (constant n "f_erased(r)")
  generate mode n (Pi _ _ _) = Right (constant n "f_erased(r)")
  generate mode n (Sigma _ _ _ _) = Right (constant n "f_erased(r)")
  generate mode n (BoxType _ _) = Right (constant n "f_erased(r)")
  generate mode n (NominalType _ _ _) = Right (constant n "f_erased(r)")
  generate mode n (VariantType _) = Right (constant n "f_erased(r)")
  generate mode n (Lambda quantity domain body) = do
    generated <- generate mode (S n) body
    let flag = if quantity == Erased then "1" else "0"
    let code = function n ("return f_lambda(r, e, " ++ flag ++ ", " ++ name generated.root ++ ");")
    Right (Output n generated.next (code :: generated.definitions))
  generate mode n (Apply function argument) = binary mode n "f_apply" function argument
  generate mode n (StringAppend left right) = binary mode n "f_append" left right
  generate mode n (StringEqual left right) = binary mode n "f_string_equal" left right
  generate mode n (BoolCase condition yes no) = ternary mode n "f_bool_case" condition yes no
  generate mode n (NominalValue _ value) = unary mode n "f_nominal" value
  generate mode n (NominalCase _ scrutinee branch) = binary mode n "f_nominal_case" scrutinee branch
  generate mode n (VariantValue _ tag Nothing) =
    Right (Output n (S n) [function n ("(void)e; return f_variant(r, e, " ++ show tag ++ ", NULL);")])
  generate mode n (VariantValue _ tag (Just value)) = do
    part <- generate mode (S n) value
    let code = function n ("return f_variant(r, e, " ++ show tag ++ ", " ++ name part.root ++ ");")
    Right (Output n part.next (code :: part.definitions))
  generate mode n (VariantCase _ scrutinee []) = Left "C backend rejects an empty variant case"
  generate mode n (VariantCase _ scrutinee branches) = do
    scrutineeCode <- generate mode (S n) scrutinee
    (next, roots, definitions) <- generateBranches mode scrutineeCode.next branches
    let code = function n ("return f_variant_case(r, e, " ++ name scrutineeCode.root ++ ", " ++
                           show (length roots) ++ ", (FEval[]){" ++ concat (intersperse "," (map name roots)) ++ "});")
    Right (Output n next (code :: (scrutineeCode.definitions ++ definitions)))
  generate mode n (UnitCase scrutinee body) = binary mode n "f_unit_case" scrutinee body
  generate mode n (IOPure value) = unary mode n "f_pure" value
  generate mode n (WriteLine text) = unary mode n "f_write" text
  generate mode n (IOBind _ _ action continuation) = binary mode n "f_bind" action continuation
  generate Binary n (IterateBinary _ _ count step initial) = ternary Binary n "f_iterate_binary" count step initial
  generate Binary n (ReadBytes capacity) = unary Binary n "f_read_bytes" capacity
  generate Binary n (WriteBytes bytes) = unary Binary n "f_write_bytes" bytes
  generate Binary n RejectBytes = Right (constant n "f_reject_bytes(r)")
  generate Binary n FlushBytes = Right (constant n "f_flush_bytes(r)")
  generate Interactive n ReadLine = Right (constant n "f_read_line(r)")
  generate Resources n ReadLine = Right (constant n "f_read_line(r)")
  generate Resources n (WithInputFile _ path body) = binary Resources n "f_with_input" path body
  generate Resources n (ReadInputFile handle) = unary Resources n "f_read_input" handle
  -- Pure pair structure is shared by modes; its contents retain the caller's gate.
  generate mode n (PairCase _ scrutinee branch) = binary mode n "f_pair_case" scrutinee branch
  generate mode n (BoxValue _ value) = unary mode n "f_nominal" value
  generate mode n (BoxCase _ scrutinee branch) = binary mode n "f_nominal_case" scrutinee branch
  generate mode n (PairValue annotation first second) =
    case weakHead typeReductionFuel annotation of
      HeadLimit _ => Left "Native pair annotation reduction budget exhausted"
      HeadForm (Sigma q r _ _) => do
        a <- generate mode (S n) first
        b <- generate mode a.next second
        let erasedFirst = if q == Erased then "1" else "0"
        let erasedSecond = if r == Erased then "1" else "0"
        let code = function n ("return f_pair(r, e, " ++ erasedFirst ++ ", " ++ erasedSecond ++ ", " ++
                               name a.root ++ ", " ++ name b.root ++ ");")
        Right (Output n b.next (code :: (a.definitions ++ b.definitions)))
      HeadForm _ => Left "Native pair annotation did not expose Sigma"
  generate mode n _ = Left "C backend does not support this computational core construct"

  generateBranches : NativeMode -> Nat -> List (Term n) -> Either String (Nat, List Nat, List String)
  generateBranches mode n [] = Right (n, [], [])
  generateBranches mode n (branch :: rest) = do
    first <- generate mode n branch
    (next, roots, definitions) <- generateBranches mode first.next rest
    Right (next, first.root :: roots, first.definitions ++ definitions)

  ternary : NativeMode -> Nat -> String -> Term n -> Term n -> Term n -> Either String Generated
  ternary mode n operation first second third = do
    a <- generate mode (S n) first
    b <- generate mode a.next second
    c <- generate mode b.next third
    let code = function n ("return " ++ operation ++ "(r, e, " ++ name a.root ++ ", " ++ name b.root ++ ", " ++ name c.root ++ ");")
    Right (Output n c.next (code :: (a.definitions ++ b.definitions ++ c.definitions)))

  unary : NativeMode -> Nat -> String -> Term n -> Either String Generated
  unary mode n operation term = do
    part <- generate mode (S n) term
    let code = function n ("return " ++ operation ++ "(r, e, " ++ name part.root ++ ");")
    Right (Output n part.next (code :: part.definitions))

  binary : NativeMode -> Nat -> String -> Term n -> Term n -> Either String Generated
  binary mode n operation first second = do
    a <- generate mode (S n) first
    b <- generate mode a.next second
    let code = function n ("return " ++ operation ++ "(r, e, " ++ name a.root ++ ", " ++ name b.root ++ ");")
    Right (Output n b.next (code :: (a.definitions ++ b.definitions)))

prototypes : Nat -> Nat -> List String
prototypes start Z = []
prototypes start (S count) = prototype start :: prototypes (S start) count

emitEntry : NativeMode -> Nat -> Nat -> Term 0 -> Either String String
emitEntry mode requests lineLimit term = do
  if mode /= Binary && containsBinaryRequest term then Left "Binary IO requires the explicit binary runner" else Right ()
  if mode == Binary && containsNonBinaryIO term then Left "Native binary entry rejects non-binary IO/references" else Right ()
  if mode == Resources && containsFileReference term
    then Left "Native resource entry rejects runtime file references" else Right ()
  case checkRuntime checkingDepth typeReductionFuel Empty term (IOType UnitType) of
    Left err => Left ("Native entry checking: " ++ show err)
    Right _ => Right ()
  if coreNodes term > 8192 then Left "Native core admission exceeds 8192 nodes" else Right ()
  if payloadSize term > payloadLimit then Left "Native literal admission exceeds 8192 characters" else Right ()
  if mode == Binary && (requests > 100000 || lineLimit > 8388608)
     then Left "Native binary admission limit exceeded" else Right ()
  if mode /= Preflight && mode /= Binary && (requests > 100000 || lineLimit > 8192)
     then Left (if mode == Resources then "Native resource admission limit exceeded"
                else "Native interactive admission limit exceeded") else Right ()
  code <- generate mode 0 term
  let entry = case mode of
        Preflight => "fibril_native_run(" ++ name code.root ++ ")"
        Interactive => "fibril_native_interactive_run(" ++ name code.root ++ ", " ++ show requests ++ ", " ++ show lineLimit ++ ")"
        Resources => "fibril_native_resource_run(" ++ name code.root ++ ", " ++ show requests ++ ", " ++ show lineLimit ++ ")"
        Binary => "fibril_native_binary_run(" ++ name code.root ++ ", " ++ show requests ++ ", " ++ show lineLimit ++ ")"
  Right ("/* Generated from checked Fibril core; experimental native subset. */\n" ++
         "#include \"fibril_runtime.h\"\n" ++ concat (prototypes 0 code.next) ++
         concat code.definitions ++ "int main(void) { return " ++ entry ++ "; }\n")

||| Original expanded term is checked before any lowering or reduction.
||| Output-only mode rejects computational read requests.
public export
emitCheckedC : Term 0 -> Either String String
emitCheckedC = emitEntry Preflight 0 0

||| Explicit incremental console entry; resource requests remain unsupported.
public export
emitCheckedInteractiveC : Nat -> Nat -> Term 0 -> Either String String
emitCheckedInteractiveC = emitEntry Interactive

||| Explicit scoped-resource entry. No caller-supplied runtime references allowed.
public export
emitCheckedResourceC : Nat -> Nat -> Term 0 -> Either String String
emitCheckedResourceC = emitEntry Resources

||| Explicit binary-only borrowed stdio. Second bound is aggregate byte capacity.
||| Compile generated C against fibril_binary_runtime.c, not fibril_runtime.c.
public export
emitCheckedBinaryC : Nat -> Nat -> Term 0 -> Either String String
emitCheckedBinaryC = emitEntry Binary
