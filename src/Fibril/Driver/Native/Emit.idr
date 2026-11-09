-- Checked core to C, independent of file/project loading and host execution.
module Fibril.Driver.Native.Emit

import Fibril.Driver.DataLowering
import Data.List
import Data.Fin
import Fibril.Core.SharedProgram
import Fibril.Core.Term
import Fibril.Core.OutputAdmission
import Fibril.Core.EffectAdmission
import Fibril.Data.Bytes
import Fibril.Core.Quantity
import Fibril.Core.Context
import Fibril.Core.Runtime
import Fibril.Core.Erased
import Fibril.Core.DataDecl
import Fibril.Core.WeakHead
import Fibril.Core.ResourceAdmission
import Fibril.Core.Limits
import Fibril.Core.Size
import Fibril.Elaboration.Expression.Payload

%default total

data NativeMode = Preflight | Interactive | Resources | Binary | Embedded

Eq NativeMode where
  Preflight == Preflight = True
  Interactive == Interactive = True
  Resources == Resources = True
  Binary == Binary = True
  Embedded == Embedded = True
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

wordRuntimeFunction : PrimOp -> Maybe String
wordRuntimeFunction WordAddOp = Just "f_word_add"
wordRuntimeFunction WordSubOp = Just "f_word_sub"
wordRuntimeFunction WordMulOp = Just "f_word_mul"
wordRuntimeFunction WordEqOp = Just "f_word_eq"
wordRuntimeFunction WordLtOp = Just "f_word_lt"
wordRuntimeFunction WordDivOp = Just "f_word_div"
wordRuntimeFunction WordRemOp = Just "f_word_rem"
wordRuntimeFunction BytesEqualOp = Just "f_bytes_equal"
wordRuntimeFunction _ = Nothing

mutual
  generate : RuntimeGlobals -> NativeMode -> Nat -> Term n -> Either String Generated
  generate globals mode n (GlobalRef key) = case globalEntry (erasedGlobals globals) key of
    Just (Erased, _, _) => Right (constant n "f_erased(r)")
    Just (Unrestricted, _, _) => Right (constant n ("f_global(r, fibril_global_" ++ show key ++ ")"))
    _ => Left "C backend rejects an unknown or linear global"
  generate globals mode n (Variable index) = Right (Output n (S n) [function n ("return f_variable(r, e, " ++ show (finToNat index) ++ ");")])
  generate globals mode n (UTF8Encode x) = unary globals mode n "f_utf8_encode" x
  generate globals mode n (UTF8Decode x) = unary globals mode n "f_utf8_decode" x
  generate globals mode n BytesType = Right (constant n "f_erased(r)")
  generate globals mode n (BytesValue value) = Right (Output n (S n) [byteLiteral n value])
  generate globals mode n (BytesAppend a b) = binary globals mode n "f_bytes_append" a b
  generate globals mode n (BytesLengthIs a b) = binary globals mode n "f_bytes_length_is" a b
  generate globals mode n (BytesIndex a b) = binary globals mode n "f_bytes_index" a b
  generate globals mode n (BytesSlice a b c) = ternary globals mode n "f_bytes_slice" a b c
  generate globals mode n (BytesShare x) = unary globals mode n "f_nominal" x
  generate globals mode n (BytesLength x) = unary globals mode n "f_bytes_length" x
  generate globals mode n (BytesOctet x) = unary globals mode n "f_bytes_octet" x
  generate globals mode n (StringValue value) = Right (Output n (S n) [literal n value])
  generate globals mode n UnitValue = Right (constant n "f_unit(r)")
  generate globals mode n (Universe _) = Right (constant n "f_erased(r)")
  generate globals mode n UnitType = Right (constant n "f_erased(r)")
  generate globals mode n BoolType = Right (constant n "f_erased(r)")
  generate globals mode n NatType = Right (constant n "f_erased(r)")
  generate globals mode n (RecType _) = Right (constant n "f_erased(r)")
  generate globals mode n (SeqType _ _) = Right (constant n "f_erased(r)")
  generate globals mode n NatZero = Right (constant n "f_nat_zero(r)")
  generate globals mode n (NatSucc tail) = unary globals mode n "f_nat_succ" tail
  generate globals mode n (RecEnd _) = Right (constant n "f_rec_end(r)")
  generate globals mode n (RecMore _ tail) = unary globals mode n "f_rec_more" tail
  generate globals mode n (SeqNil _) = Right (constant n "f_seq_nil(r)")
  generate globals mode n (SeqCons _ head tail) = binary globals mode n "f_seq_cons" head tail
  generate globals mode n (NatRec _ base step value) = ternary globals mode n "f_nat_rec" base step value
  generate globals mode n (NatRecRuntime _ base step value) = ternary globals mode n "f_nat_rec_runtime" base step value
  generate globals mode n (RecFold _ base step value) = ternary globals mode n "f_rec_fold" base step value
  generate globals mode n (SeqFold _ base step value) = ternary globals mode n "f_seq_fold" base step value
  generate globals mode n (RecCase _ value base more) = ternary globals mode n "f_rec_case" value base more
  generate globals mode n (NatCase _ value base more) = ternary globals mode n "f_nat_case" value base more
  generate globals mode n (SeqCase _ value base cons) = ternary globals mode n "f_seq_case" value base cons
  generate globals mode n BoolTrue = Right (constant n "f_bool(r, 1)")
  generate globals mode n BoolFalse = Right (constant n "f_bool(r, 0)")
  generate globals mode n StringType = Right (constant n "f_erased(r)")
  generate globals mode n (IOType _) = Right (constant n "f_erased(r)")
  generate globals mode n (FileHandleType _) = Right (constant n "f_erased(r)")
  generate globals mode n (Pi _ _ _) = Right (constant n "f_erased(r)")
  generate globals mode n (Sigma _ _ _ _) = Right (constant n "f_erased(r)")
  generate globals mode n (BoxType _ _) = Right (constant n "f_erased(r)")
  generate globals mode n (NominalType _ _ _) = Right (constant n "f_erased(r)")
  generate globals mode n (VariantType _) = Right (constant n "f_erased(r)")
  generate globals mode n (Lambda quantity domain body) = do
    generated <- generate globals mode (S n) body
    let flag = if quantity == Erased then "1" else "0"
    let code = function n ("return f_lambda(r, e, " ++ flag ++ ", " ++ name generated.root ++ ");")
    Right (Output n generated.next (code :: generated.definitions))
  generate globals mode n (DataType _) = Right (constant n "f_erased(r)")
  generate globals mode n (DataCon key index leading) =
    case dataDeclaration (erasedGlobals globals) key of
      Nothing => Left "C backend: unknown general data family"
      Just decl => case constructorType decl index of
        Nothing => Left "C backend: unknown general data constructor"
        Just chain => case buildConstructor index leading (fieldQuantities leading chain) (the (Term 0) chain) of
          Nothing => Left "C backend could not lower a general data constructor"
          -- The lowered term contains only lambdas, pairs and variants, so lowering it terminates.
          Just lowered => assert_total (generate globals mode n lowered)
  generate globals mode n (DataCase key _ scrutinee branches) =
    case dataDeclaration (erasedGlobals globals) key of
      Nothing => Left "C backend: unknown general data family"
      Just decl => case wrapBranches decl 0 branches of
        Nothing => Left "C backend could not lower a general data case"
        Just wrapped => assert_total (generate globals mode n (VariantCase NatType scrutinee wrapped))
  generate globals mode n (Fix _ body) = do
    generated <- generate globals mode (S n) body
    let code = function n ("return f_fix(r, e, " ++ name generated.root ++ ");")
    Right (Output n generated.next (code :: generated.definitions))
  -- A variable already denotes a lazy cell. Preserve that cell and its owner
  -- instead of allocating a thunk whose only work would be another lookup.
  generate globals mode n (Apply callee (Variable index)) = do
    generated <- generate globals mode (S n) callee
    let code = function n ("return f_apply_variable(r, e, " ++ name generated.root ++
                          ", " ++ show (finToNat index) ++ ");")
    Right (Output n generated.next (code :: generated.definitions))
  generate globals mode n (Apply function argument) = binary globals mode n "f_apply" function argument
  generate globals mode n (StringAppend left right) = binary globals mode n "f_append" left right
  generate globals mode n (Prim WordTypeOp _) = Right (constant n "f_erased(r)")
  generate globals mode n (Prim (WordLitOp value) []) =
    if value < 0 || value >= wordModulus
      then Left "C backend rejects a Word literal outside 0 .. 2^64-1"
      else Right (constant n ("f_word(r, UINT64_C(" ++ show value ++ "))"))
  generate globals mode n (Prim WordFromNatOp [argument]) = unary globals mode n "f_word_from_nat" argument
  generate globals mode n (Prim WordToStringOp [argument]) = unary globals mode n "f_word_to_string" argument
  generate globals mode n (Prim operation [left, right]) =
    case wordRuntimeFunction operation of
      Just function => binary globals mode n function left right
      Nothing => Left "C backend rejects an unsupported primitive operation"
  generate globals mode n (Prim _ _) = Left "C backend rejects a malformed primitive application"
  generate globals mode n (StringEqual left right) = binary globals mode n "f_string_equal" left right
  generate globals mode n (BoolCase condition yes no) = ternary globals mode n "f_bool_case" condition yes no
  generate globals mode n (NominalValue _ value) = unary globals mode n "f_nominal" value
  generate globals mode n (NominalCase _ scrutinee branch) = binary globals mode n "f_nominal_case" scrutinee branch
  generate globals mode n (VariantValue _ tag Nothing) =
    Right (Output n (S n) [function n ("(void)e; return f_variant(r, e, " ++ show tag ++ ", NULL);")])
  generate globals mode n (VariantValue _ tag (Just value)) = do
    part <- generate globals mode (S n) value
    let code = function n ("return f_variant(r, e, " ++ show tag ++ ", " ++ name part.root ++ ");")
    Right (Output n part.next (code :: part.definitions))
  generate globals mode n (VariantCase _ scrutinee []) = Left "C backend rejects an empty variant case"
  generate globals mode n (VariantCase _ scrutinee branches) = do
    scrutineeCode <- generate globals mode (S n) scrutinee
    (next, roots, definitions) <- generateBranches globals mode scrutineeCode.next branches
    let code = function n ("return f_variant_case(r, e, " ++ name scrutineeCode.root ++ ", " ++
                           show (length roots) ++ ", (FEval[]){" ++ concat (intersperse "," (map name roots)) ++ "});")
    Right (Output n next (code :: (scrutineeCode.definitions ++ definitions)))
  generate globals mode n (UnitCase scrutinee body) = binary globals mode n "f_unit_case" scrutinee body
  generate globals mode n (IOPure value) = unary globals mode n "f_pure" value
  generate globals mode n (WriteLine text) = unary globals mode n "f_write" text
  generate globals mode n (IOBind _ _ action continuation) = binary globals mode n "f_bind" action continuation
  generate globals Binary n (IterateBinary _ _ count step initial) = ternary globals Binary n "f_iterate_binary" count step initial
  generate globals Binary n (ReadBytes capacity) = unary globals Binary n "f_read_bytes" capacity
  generate globals Binary n (WriteBytes bytes) = unary globals Binary n "f_write_bytes" bytes
  generate globals Binary n RejectBytes = Right (constant n "f_reject_bytes(r)")
  generate globals Binary n FlushBytes = Right (constant n "f_flush_bytes(r)")
  generate globals Interactive n ReadLine = Right (constant n "f_read_line(r)")
  generate globals Resources n ReadLine = Right (constant n "f_read_line(r)")
  generate globals Resources n (WithInputFile _ path body) = binary globals Resources n "f_with_input" path body
  generate globals Resources n (ReadInputFile handle) = unary globals Resources n "f_read_input" handle
  -- Pure pair structure is shared by modes; its contents retain the caller's gate.
  generate globals mode n (PairCase _ scrutinee branch) = binary globals mode n "f_pair_case" scrutinee branch
  generate globals mode n (BoxValue _ value) = unary globals mode n "f_nominal" value
  generate globals mode n (BoxCase _ scrutinee branch) = binary globals mode n "f_nominal_case" scrutinee branch
  generate globals mode n (PairValue annotation first second) =
    case weakHeadGlobals (globalValue (erasedGlobals globals)) typeReductionFuel annotation of
      HeadLimit _ => Left "Native pair annotation reduction budget exhausted"
      HeadForm (Sigma q r _ _) => do
        a <- generate globals mode (S n) first
        b <- generate globals mode a.next second
        let erasedFirst = if q == Erased then "1" else "0"
        let erasedSecond = if r == Erased then "1" else "0"
        let code = function n ("return f_pair(r, e, " ++ erasedFirst ++ ", " ++ erasedSecond ++ ", " ++
                               name a.root ++ ", " ++ name b.root ++ ");")
        Right (Output n b.next (code :: (a.definitions ++ b.definitions)))
      HeadForm _ => Left "Native pair annotation did not expose Sigma"
  generate globals mode n (WithRegion resultType body) =
    -- The entry checker may see this node already reduced, so the emitter enforces copyable results itself.
    case checkRegionResultGlobals (erasedGlobals globals) typeReductionFuel resultType of
      Left err => Left ("Native region result: " ++ show err)
      Right () => unary globals mode n "f_with_region" body
  generate globals mode n _ = Left "C backend does not support this computational core construct"

  generateBranches : RuntimeGlobals -> NativeMode -> Nat -> List (Term n) -> Either String (Nat, List Nat, List String)
  generateBranches globals mode n [] = Right (n, [], [])
  generateBranches globals mode n (branch :: rest) = do
    first <- generate globals mode n branch
    (next, roots, definitions) <- generateBranches globals mode first.next rest
    Right (next, first.root :: roots, first.definitions ++ definitions)

  ternary : RuntimeGlobals -> NativeMode -> Nat -> String -> Term n -> Term n -> Term n -> Either String Generated
  ternary globals mode n operation first second third = do
    a <- generate globals mode (S n) first
    b <- generate globals mode a.next second
    c <- generate globals mode b.next third
    let code = function n ("return " ++ operation ++ "(r, e, " ++ name a.root ++ ", " ++ name b.root ++ ", " ++ name c.root ++ ");")
    Right (Output n c.next (code :: (a.definitions ++ b.definitions ++ c.definitions)))

  unary : RuntimeGlobals -> NativeMode -> Nat -> String -> Term n -> Either String Generated
  unary globals mode n operation term = do
    part <- generate globals mode (S n) term
    let code = function n ("return " ++ operation ++ "(r, e, " ++ name part.root ++ ");")
    Right (Output n part.next (code :: part.definitions))

  binary : RuntimeGlobals -> NativeMode -> Nat -> String -> Term n -> Term n -> Either String Generated
  binary globals mode n operation first second = do
    a <- generate globals mode (S n) first
    b <- generate globals mode a.next second
    let code = function n ("return " ++ operation ++ "(r, e, " ++ name a.root ++ ", " ++ name b.root ++ ");")
    Right (Output n b.next (code :: (a.definitions ++ b.definitions)))

prototypes : Nat -> Nat -> List String
prototypes start Z = []
prototypes start (S count) = prototype start :: prototypes (S start) count

generateGlobals : RuntimeGlobals -> NativeMode -> Nat -> List GlobalDeclaration ->
                  Either String (Nat, List String, List String)
generateGlobals globals mode next [] = Right (next, [], [])
generateGlobals globals mode next ((key, q, ty, body) :: rest) = do
  code <- generate globals mode next body
  (end, definitions, wrappers) <- generateGlobals globals mode code.next rest
  let wrapper = "FValue *fibril_global_" ++ show key ++
        "(FRuntime *r, FEnv *e) { (void)e; return " ++ name code.root ++ "(r, NULL); }\n"
  Right (end, code.definitions ++ definitions, wrapper :: wrappers)

emitEntryGlobals : RuntimeGlobals -> NativeMode -> Nat -> Nat -> Term 0 -> Either String String
emitEntryGlobals globals mode requests lineLimit term = do
  declarations <- reachableGlobals globals term
  let syntax : List (Term 0) = term :: concatMap (\(_, _, ty, body) => [ty, body]) declarations
  let scan = map maskGlobalRefs syntax
  if mode == Embedded && not (all (outputOnly True) scan)
    then Left "Embedded profile rejects input, binary transport and file references, including erased/dead syntax" else Right ()
  if mode /= Binary && any containsBinaryRequest scan then Left "Binary IO requires the explicit binary runner" else Right ()
  if mode == Binary && any containsNonBinaryIO scan then Left "Native binary entry rejects non-binary IO/references" else Right ()
  if any containsFileReference scan
    then Left "Native resource entry rejects runtime file references" else Right ()
  case checkRuntimeGlobals globals checkingDepth typeReductionFuel Empty term (IOType UnitType) of
    Left err => Left ("Native entry checking: " ++ show err)
    Right _ => Right ()
  if sharedProgramNodes term declarations > 8192 then Left "Native core admission exceeds 8192 nodes" else Right ()
  if sharedProgramPayload term declarations > payloadLimit then Left "Native literal admission exceeds 8192 characters" else Right ()
  if mode == Binary && (requests > 100000 || lineLimit > 8388608)
     then Left "Native binary admission limit exceeded" else Right ()
  if mode /= Preflight && mode /= Binary && (requests > 100000 || lineLimit > 8192)
     then Left (if mode == Resources then "Native resource admission limit exceeded"
                else "Native interactive admission limit exceeded") else Right ()
  (next, definitions, globalCode) <- generateGlobals globals mode 0 declarations
  code <- generate globals mode next term
  let entry = case mode of
        Embedded => ""
        Preflight => "fibril_native_run(" ++ name code.root ++ ")"
        Interactive => "fibril_native_interactive_run(" ++ name code.root ++ ", " ++ show requests ++ ", " ++ show lineLimit ++ ")"
        Resources => "fibril_native_resource_run(" ++ name code.root ++ ", " ++ show requests ++ ", " ++ show lineLimit ++ ")"
        Binary => "fibril_native_binary_run(" ++ name code.root ++ ", " ++ show requests ++ ", " ++ show lineLimit ++ ")"
  let mainCode = "int main(void) { return " ++ entry ++ "; }\n"
  let entryCode = if mode == Embedded
        then "FNativeResult fibril_program_embed_arena(const FNativeHost *host, FEmbeddedArena *arena) { return fibril_native_embed_arena(" ++ name code.root ++ ", host, arena); }\n"
        else if mode == Preflight
        then "FNativeResult fibril_program_embed(const FNativeHost *host) { return fibril_native_embed(" ++ name code.root ++ ", host); }\n" ++
             "#ifndef FIBRIL_EMBED_ONLY\n" ++ mainCode ++ "#endif\n"
        else if mode == Binary
          then "FBinaryResult fibril_program_binary_embed(const FByteAdapters *host) { return fibril_native_binary_embed(" ++ name code.root ++ ", " ++ show requests ++ ", " ++ show lineLimit ++ ", host); }\n" ++
               "#ifndef FIBRIL_EMBED_ONLY\n" ++ mainCode ++ "#endif\n"
          else mainCode
  let header = if mode == Binary then "fibril_binary_embed.h" else
        if mode == Embedded then "fibril_embedded.h" else "fibril_runtime.h"
  Right ("/* Generated from checked Fibril core; experimental native subset. */\n" ++
         "#include \"" ++ header ++ "\"\n" ++ concat (map (\(key, _, _, _) => "FValue *fibril_global_" ++ show key ++ "(FRuntime *, FEnv *);\n") declarations) ++
         concat (prototypes 0 code.next) ++ concat globalCode ++ concat definitions ++
         concat code.definitions ++ entryCode)

emitEntry : NativeMode -> Nat -> Nat -> Term 0 -> Either String String
emitEntry = emitEntryGlobals emptyRuntimeGlobals

||| Shared-graph console emission: each reachable declaration is checked on
||| admission, scanned in full and emitted once; references do not inline bodies.
public export
emitCheckedCGlobals : RuntimeGlobals -> Term 0 -> Either String String
emitCheckedCGlobals globals = emitEntryGlobals globals Preflight 0 0

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

public export
emitCheckedBinaryCGlobals : RuntimeGlobals -> Nat -> Nat -> Term 0 -> Either String String
emitCheckedBinaryCGlobals globals = emitEntryGlobals globals Binary

||| Portable output-only C entry using caller-owned typed pools; no default main.
public export
emitCheckedEmbeddedCGlobals : RuntimeGlobals -> Term 0 -> Either String String
emitCheckedEmbeddedCGlobals globals = emitEntryGlobals globals Embedded 0 0

public export
emitCheckedEmbeddedC : Term 0 -> Either String String
emitCheckedEmbeddedC = emitEntry Embedded 0 0
