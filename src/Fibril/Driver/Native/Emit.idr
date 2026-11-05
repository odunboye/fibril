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
  generate : Nat -> Term n -> Either String Generated
  generate n (Variable index) = Right (Output n (S n) [function n ("return f_variable(r, e, " ++ show (finToNat index) ++ ");")])
  generate n (StringValue value) = Right (Output n (S n) [literal n value])
  generate n UnitValue = Right (constant n "f_unit(r)")
  generate n (Universe _) = Right (constant n "f_erased(r)")
  generate n UnitType = Right (constant n "f_erased(r)")
  generate n BoolType = Right (constant n "f_erased(r)")
  generate n BoolTrue = Right (constant n "f_bool(r, 1)")
  generate n BoolFalse = Right (constant n "f_bool(r, 0)")
  generate n StringType = Right (constant n "f_erased(r)")
  generate n (IOType _) = Right (constant n "f_erased(r)")
  generate n (Pi _ _ _) = Right (constant n "f_erased(r)")
  generate n (Sigma _ _ _ _) = Right (constant n "f_erased(r)")
  generate n (BoxType _ _) = Right (constant n "f_erased(r)")
  generate n (NominalType _ _ _) = Right (constant n "f_erased(r)")
  generate n (VariantType _) = Right (constant n "f_erased(r)")
  generate n (Lambda quantity domain body) = do
    generated <- generate (S n) body
    let flag = if quantity == Erased then "1" else "0"
    let code = function n ("return f_lambda(r, e, " ++ flag ++ ", " ++ name generated.root ++ ");")
    Right (Output n generated.next (code :: generated.definitions))
  generate n (Apply function argument) = binary n "f_apply" function argument
  generate n (StringAppend left right) = binary n "f_append" left right
  generate n (StringEqual left right) = binary n "f_string_equal" left right
  generate n (BoolCase condition yes no) = ternary n "f_bool_case" condition yes no
  generate n (NominalValue _ value) = unary n "f_nominal" value
  generate n (NominalCase _ scrutinee branch) = binary n "f_nominal_case" scrutinee branch
  generate n (VariantValue _ tag Nothing) =
    Right (Output n (S n) [function n ("(void)e; return f_variant(r, e, " ++ show tag ++ ", NULL);")])
  generate n (VariantValue _ tag (Just value)) = do
    part <- generate (S n) value
    let code = function n ("return f_variant(r, e, " ++ show tag ++ ", " ++ name part.root ++ ");")
    Right (Output n part.next (code :: part.definitions))
  generate n (VariantCase _ scrutinee []) = Left "C backend rejects an empty variant case"
  generate n (VariantCase _ scrutinee branches) = do
    scrutineeCode <- generate (S n) scrutinee
    (next, roots, definitions) <- generateBranches scrutineeCode.next branches
    let code = function n ("return f_variant_case(r, e, " ++ name scrutineeCode.root ++ ", " ++
                           show (length roots) ++ ", (FEval[]){" ++ concat (intersperse "," (map name roots)) ++ "});")
    Right (Output n next (code :: (scrutineeCode.definitions ++ definitions)))
  generate n (UnitCase scrutinee body) = binary n "f_unit_case" scrutinee body
  generate n (IOPure value) = unary n "f_pure" value
  generate n (WriteLine text) = unary n "f_write" text
  generate n (IOBind _ _ action continuation) = binary n "f_bind" action continuation
  generate n _ = Left "C backend does not support this computational core construct"

  generateBranches : Nat -> List (Term n) -> Either String (Nat, List Nat, List String)
  generateBranches n [] = Right (n, [], [])
  generateBranches n (branch :: rest) = do
    first <- generate n branch
    (next, roots, definitions) <- generateBranches first.next rest
    Right (next, first.root :: roots, first.definitions ++ definitions)

  ternary : Nat -> String -> Term n -> Term n -> Term n -> Either String Generated
  ternary n operation first second third = do
    a <- generate (S n) first
    b <- generate a.next second
    c <- generate b.next third
    let code = function n ("return " ++ operation ++ "(r, e, " ++ name a.root ++ ", " ++ name b.root ++ ", " ++ name c.root ++ ");")
    Right (Output n c.next (code :: (a.definitions ++ b.definitions ++ c.definitions)))

  unary : Nat -> String -> Term n -> Either String Generated
  unary n operation term = do
    part <- generate (S n) term
    let code = function n ("return " ++ operation ++ "(r, e, " ++ name part.root ++ ");")
    Right (Output n part.next (code :: part.definitions))

  binary : Nat -> String -> Term n -> Term n -> Either String Generated
  binary n operation first second = do
    a <- generate (S n) first
    b <- generate a.next second
    let code = function n ("return " ++ operation ++ "(r, e, " ++ name a.root ++ ", " ++ name b.root ++ ");")
    Right (Output n b.next (code :: (a.definitions ++ b.definitions)))

prototypes : Nat -> Nat -> List String
prototypes start Z = []
prototypes start (S count) = prototype start :: prototypes (S start) count

||| Original expanded term is checked before any lowering or reduction.
public export
emitCheckedC : Term 0 -> Either String String
emitCheckedC term = do
  case checkRuntime checkingDepth typeReductionFuel Empty term (IOType UnitType) of
    Left err => Left ("Native entry checking: " ++ show err)
    Right _ => Right ()
  if coreNodes term > 8192 then Left "Native core admission exceeds 8192 nodes" else Right ()
  if payloadSize term > payloadLimit then Left "Native literal admission exceeds 8192 characters" else Right ()
  code <- generate 0 term
  Right ("/* Generated from checked Fibril core; experimental native subset. */\n" ++
         "#include \"fibril_runtime.h\"\n" ++ concat (prototypes 0 code.next) ++
         concat code.definitions ++ "int main(void) { return fibril_native_run(" ++ name code.root ++ "); }\n")
