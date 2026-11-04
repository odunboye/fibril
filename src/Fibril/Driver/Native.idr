-- Checked core to C source. No reference evaluation or host effect execution.
module Fibril.Driver.Native

import Data.List
import Data.Fin
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Context
import Fibril.Core.Runtime
import Fibril.Core.Limits
import Fibril.Core.Size
import Fibril.Elaboration.Expression.Payload
import Fibril.Source.File
import Fibril.Source.Diagnostic
import Fibril.Driver.Check
import Fibril.Driver.ModuleCheck
import Fibril.Driver.ModuleGraph

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
  generate n (UnitCase scrutinee body) = binary n "f_unit_case" scrutinee body
  generate n (IOPure value) = unary n "f_pure" value
  generate n (WriteLine text) = unary n "f_write" text
  generate n (IOBind _ _ action continuation) = binary n "f_bind" action continuation
  generate n _ = Left "C backend does not support this computational core construct"

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

public export
emitCFile : String -> IO (Either String String)
emitCFile path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (renderFileError path (show err))
    Right source => case resolveSource source of
      Left err => Left (renderDriverError path source (FrontendFailure err))
      Right term => emitCheckedC term

public export
emitCProject : String -> String -> IO (Either String String)
emitCProject root entry = do
  checked <- checkProject root entry
  pure $ case checked of
    Left err => Left (renderGraphError err)
    Right project => emitCheckedC project.term

public export
emitCPackage : String -> IO (Either String String)
emitCPackage manifest = do
  checked <- checkPackage manifest
  pure $ case checked of
    Left err => Left (renderGraphError err)
    Right project => emitCheckedC project.term
