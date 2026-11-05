-- Checked core to C, independent of file/project loading and host execution.
module Fibril.Driver.Native.Emit

import Data.List
import Data.Fin
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Context
import Fibril.Core.Runtime
import Fibril.Core.Limits
import Fibril.Core.Size
import Fibril.Elaboration.Expression.Payload

%default total

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

constant : Nat -> String -> Generated
constant n expr = Output n (S n) [function n ("(void)e; return " ++ expr ++ ";")]

mutual
  generate : Bool -> Nat -> Term n -> Either String Generated
  generate interactive n (Variable index) = Right (Output n (S n) [function n ("return f_variable(r, e, " ++ show (finToNat index) ++ ");")])
  generate interactive n (StringValue value) = Right (Output n (S n) [literal n value])
  generate interactive n UnitValue = Right (constant n "f_unit(r)")
  generate interactive n (Universe _) = Right (constant n "f_erased(r)")
  generate interactive n UnitType = Right (constant n "f_erased(r)")
  generate interactive n BoolType = Right (constant n "f_erased(r)")
  generate interactive n BoolTrue = Right (constant n "f_bool(r, 1)")
  generate interactive n BoolFalse = Right (constant n "f_bool(r, 0)")
  generate interactive n StringType = Right (constant n "f_erased(r)")
  generate interactive n (IOType _) = Right (constant n "f_erased(r)")
  generate interactive n (FileHandleType _) = Right (constant n "f_erased(r)")
  generate interactive n (Pi _ _ _) = Right (constant n "f_erased(r)")
  generate interactive n (Sigma _ _ _ _) = Right (constant n "f_erased(r)")
  generate interactive n (BoxType _ _) = Right (constant n "f_erased(r)")
  generate interactive n (NominalType _ _ _) = Right (constant n "f_erased(r)")
  generate interactive n (VariantType _) = Right (constant n "f_erased(r)")
  generate interactive n (Lambda quantity domain body) = do
    generated <- generate interactive (S n) body
    let flag = if quantity == Erased then "1" else "0"
    let code = function n ("return f_lambda(r, e, " ++ flag ++ ", " ++ name generated.root ++ ");")
    Right (Output n generated.next (code :: generated.definitions))
  generate interactive n (Apply function argument) = binary interactive n "f_apply" function argument
  generate interactive n (StringAppend left right) = binary interactive n "f_append" left right
  generate interactive n (StringEqual left right) = binary interactive n "f_string_equal" left right
  generate interactive n (BoolCase condition yes no) = ternary interactive n "f_bool_case" condition yes no
  generate interactive n (NominalValue _ value) = unary interactive n "f_nominal" value
  generate interactive n (NominalCase _ scrutinee branch) = binary interactive n "f_nominal_case" scrutinee branch
  generate interactive n (VariantValue _ tag Nothing) =
    Right (Output n (S n) [function n ("(void)e; return f_variant(r, e, " ++ show tag ++ ", NULL);")])
  generate interactive n (VariantValue _ tag (Just value)) = do
    part <- generate interactive (S n) value
    let code = function n ("return f_variant(r, e, " ++ show tag ++ ", " ++ name part.root ++ ");")
    Right (Output n part.next (code :: part.definitions))
  generate interactive n (VariantCase _ scrutinee []) = Left "C backend rejects an empty variant case"
  generate interactive n (VariantCase _ scrutinee branches) = do
    scrutineeCode <- generate interactive (S n) scrutinee
    (next, roots, definitions) <- generateBranches interactive scrutineeCode.next branches
    let code = function n ("return f_variant_case(r, e, " ++ name scrutineeCode.root ++ ", " ++
                           show (length roots) ++ ", (FEval[]){" ++ concat (intersperse "," (map name roots)) ++ "});")
    Right (Output n next (code :: (scrutineeCode.definitions ++ definitions)))
  generate interactive n (UnitCase scrutinee body) = binary interactive n "f_unit_case" scrutinee body
  generate interactive n (IOPure value) = unary interactive n "f_pure" value
  generate interactive n (WriteLine text) = unary interactive n "f_write" text
  generate interactive n (IOBind _ _ action continuation) = binary interactive n "f_bind" action continuation
  generate True n ReadLine = Right (constant n "f_read_line(r)")
  generate interactive n _ = Left "C backend does not support this computational core construct"

  generateBranches : Bool -> Nat -> List (Term n) -> Either String (Nat, List Nat, List String)
  generateBranches interactive n [] = Right (n, [], [])
  generateBranches interactive n (branch :: rest) = do
    first <- generate interactive n branch
    (next, roots, definitions) <- generateBranches interactive first.next rest
    Right (next, first.root :: roots, first.definitions ++ definitions)

  ternary : Bool -> Nat -> String -> Term n -> Term n -> Term n -> Either String Generated
  ternary interactive n operation first second third = do
    a <- generate interactive (S n) first
    b <- generate interactive a.next second
    c <- generate interactive b.next third
    let code = function n ("return " ++ operation ++ "(r, e, " ++ name a.root ++ ", " ++ name b.root ++ ", " ++ name c.root ++ ");")
    Right (Output n c.next (code :: (a.definitions ++ b.definitions ++ c.definitions)))

  unary : Bool -> Nat -> String -> Term n -> Either String Generated
  unary interactive n operation term = do
    part <- generate interactive (S n) term
    let code = function n ("return " ++ operation ++ "(r, e, " ++ name part.root ++ ");")
    Right (Output n part.next (code :: part.definitions))

  binary : Bool -> Nat -> String -> Term n -> Term n -> Either String Generated
  binary interactive n operation first second = do
    a <- generate interactive (S n) first
    b <- generate interactive a.next second
    let code = function n ("return " ++ operation ++ "(r, e, " ++ name a.root ++ ", " ++ name b.root ++ ");")
    Right (Output n b.next (code :: (a.definitions ++ b.definitions)))

prototypes : Nat -> Nat -> List String
prototypes start Z = []
prototypes start (S count) = prototype start :: prototypes (S start) count

emitEntry : Bool -> Nat -> Nat -> Term 0 -> Either String String
emitEntry interactive requests lineLimit term = do
  case checkRuntime checkingDepth typeReductionFuel Empty term (IOType UnitType) of
    Left err => Left ("Native entry checking: " ++ show err)
    Right _ => Right ()
  if coreNodes term > 8192 then Left "Native core admission exceeds 8192 nodes" else Right ()
  if payloadSize term > payloadLimit then Left "Native literal admission exceeds 8192 characters" else Right ()
  if interactive && (requests > 100000 || lineLimit > 8192)
     then Left "Native interactive admission limit exceeded" else Right ()
  code <- generate interactive 0 term
  let entry = if interactive
        then "fibril_native_interactive_run(" ++ name code.root ++ ", " ++ show requests ++ ", " ++ show lineLimit ++ ")"
        else "fibril_native_run(" ++ name code.root ++ ")"
  Right ("/* Generated from checked Fibril core; experimental native subset. */\n" ++
         "#include \"fibril_runtime.h\"\n" ++ concat (prototypes 0 code.next) ++
         concat code.definitions ++ "int main(void) { return " ++ entry ++ "; }\n")

||| Original expanded term is checked before any lowering or reduction.
||| Output-only mode rejects computational read requests.
public export
emitCheckedC : Term 0 -> Either String String
emitCheckedC = emitEntry False 0 0

||| Explicit incremental entry; later failures can follow already visible output.
public export
emitCheckedInteractiveC : Nat -> Nat -> Term 0 -> Either String String
emitCheckedInteractiveC = emitEntry True
