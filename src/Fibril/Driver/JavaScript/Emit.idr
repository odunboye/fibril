-- Original checked core to an immutable runtime instruction tree and bundled ES module.
module Fibril.Driver.JavaScript.Emit

import Data.Fin
import Data.List
import Fibril.Core.DataDecl
import Fibril.Core.Context
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.SharedProgram
import Fibril.Core.Limits
import Fibril.Core.WeakHead
import Fibril.Data.Bytes
import Fibril.Elaboration.Expression.Payload
import Fibril.Driver.JSON
import Fibril.Driver.DataLowering
import Fibril.Driver.JavaScript.Admission
import Fibril.Driver.JavaScript.RuntimeSource

%default total

node : String -> List String -> String
node tag args = jsonArray (jsonString tag :: args)

flag : Quantity -> String
flag Erased = "true"
flag _ = "false"

wordOperation : PrimOp -> Maybe String
wordOperation WordAddOp = Just "wordAdd"
wordOperation WordSubOp = Just "wordSub"
wordOperation WordMulOp = Just "wordMul"
wordOperation WordEqOp = Just "wordEq"
wordOperation WordLtOp = Just "wordLt"
wordOperation WordDivOp = Just "wordDiv"
wordOperation WordRemOp = Just "wordRem"
wordOperation _ = Nothing

mutual
  generate : Nat -> RuntimeGlobals -> Term n -> Either String String
  generate Z globals _ = Left "JavaScript lowering depth exhausted"
  generate (S fuel) globals (GlobalRef key) = case globalEntry (erasedGlobals globals) key of
    Just (Erased, _, _) => Right (node "erased" [])
    Just (Unrestricted, _, _) => Right (node "global" [show key])
    _ => Left "JavaScript backend rejects an unknown or linear global"
  generate (S fuel) globals (Variable i) = Right (node "var" [show (finToNat i)])
  generate (S fuel) globals (Lambda q _ body) = do
    code <- generate fuel globals body
    Right (node "lambda" [flag q, code])
  generate (S fuel) globals (Fix _ body) = unary fuel globals "fix" body
  generate (S fuel) globals (Apply fn arg) = binary fuel globals "apply" fn arg
  generate (S fuel) globals (StringValue text) = Right (node "string" [jsonString text])
  generate (S fuel) globals (BytesValue bytes) = Right (node "bytes" [jsonArray (map show (Fibril.Data.Bytes.toList bytes))])
  generate (S fuel) globals UnitValue = Right (node "unit" [])
  generate (S fuel) globals BoolTrue = Right (node "bool" ["true"])
  generate (S fuel) globals BoolFalse = Right (node "bool" ["false"])
  generate (S fuel) globals NatZero = Right (node "zero" [])
  generate (S fuel) globals (NatSucc x) = unary fuel globals "succ" x
  generate (S fuel) globals (RecEnd _) = Right (node "end" [])
  generate (S fuel) globals (RecMore _ x) = unary fuel globals "more" x
  generate (S fuel) globals (SeqNil _) = Right (node "nil" [])
  generate (S fuel) globals (SeqCons _ head tail) = binary fuel globals "cons" head tail
  generate (S fuel) globals (NatRec _ base step value) = ternary fuel globals "natFold" base step value
  generate (S fuel) globals (NatRecRuntime _ base step value) = ternary fuel globals "natRuntimeFold" base step value
  generate (S fuel) globals (RecFold _ base step value) = ternary fuel globals "recFold" base step value
  generate (S fuel) globals (SeqFold _ base step value) = ternary fuel globals "seqFold" base step value
  generate (S fuel) globals (NatCase _ value base step) = ternary fuel globals "natCase" value base step
  generate (S fuel) globals (RecCase _ value base step) = ternary fuel globals "recCase" value base step
  generate (S fuel) globals (SeqCase _ value base step) = ternary fuel globals "seqCase" value base step
  generate (S fuel) globals (DataCon key index leading) = do
    decl <- maybe (Left "JavaScript backend: unknown data family") Right (dataDeclaration (erasedGlobals globals) key)
    chain <- maybe (Left "JavaScript backend: unknown constructor") Right (constructorType decl index)
    lowered <- maybe (Left "JavaScript backend: constructor lowering failed") Right
      (buildConstructor index leading (fieldQuantities leading chain) (the (Term 0) chain))
    generate fuel globals lowered
  generate (S fuel) globals (DataCase key _ value branches) = do
    decl <- maybe (Left "JavaScript backend: unknown case family") Right (dataDeclaration (erasedGlobals globals) key)
    wrapped <- maybe (Left "JavaScript backend: case lowering failed") Right (wrapBranches decl 0 branches)
    generate fuel globals (VariantCase NatType value wrapped)
  generate (S fuel) globals (VariantValue _ tag Nothing) = Right (node "variant" [show tag, "null"])
  generate (S fuel) globals (VariantValue _ tag (Just payload)) = do
    code <- generate fuel globals payload
    Right (node "variant" [show tag, code])
  generate (S fuel) globals (VariantCase _ value branches) = do
    scrutinee <- generate fuel globals value
    choices <- generateBranches fuel globals branches
    Right (node "variantCase" [scrutinee, jsonArray choices])
  generate (S fuel) globals (NominalValue _ value) = unary fuel globals "nominal" value
  generate (S fuel) globals (NominalCase _ value branch) = binary fuel globals "nominalCase" value branch
  generate (S fuel) globals (BoxValue _ value) = unary fuel globals "nominal" value
  generate (S fuel) globals (BoxCase _ value branch) = binary fuel globals "nominalCase" value branch
  generate (S fuel) globals (PairValue annotation first second) = case weakHeadGlobals (globalValue (erasedGlobals globals)) typeReductionFuel annotation of
    HeadForm (Sigma q r _ _) => do
      a <- generate fuel globals first
      b <- generate fuel globals second
      Right (node "pair" [flag q, flag r, a, b])
    _ => Left "JavaScript pair annotation did not expose Sigma within budget"
  generate (S fuel) globals (PairCase _ value branch) = binary fuel globals "pairCase" value branch
  generate (S fuel) globals (UnitCase value body) = binary fuel globals "unitCase" value body
  generate (S fuel) globals (BoolCase condition yes no) = ternary fuel globals "if" condition yes no
  generate (S fuel) globals (StringAppend a b) = binary fuel globals "append" a b
  generate (S fuel) globals (StringEqual a b) = binary fuel globals "stringEq" a b
  generate (S fuel) globals (UTF8Encode x) = unary fuel globals "utf8Encode" x
  generate (S fuel) globals (UTF8Decode x) = unary fuel globals "utf8Decode" x
  generate (S fuel) globals (BytesAppend a b) = binary fuel globals "bytesAppend" a b
  generate (S fuel) globals (BytesShare x) = unary fuel globals "bytesShare" x
  generate (S fuel) globals (BytesLength x) = unary fuel globals "bytesLength" x
  generate (S fuel) globals (BytesOctet x) = unary fuel globals "bytesOctet" x
  generate (S fuel) globals (BytesLengthIs a b) = binary fuel globals "bytesLengthIs" a b
  generate (S fuel) globals (BytesIndex a b) = binary fuel globals "bytesIndex" a b
  generate (S fuel) globals (BytesSlice a b c) = ternary fuel globals "bytesSlice" a b c
  generate (S fuel) globals (IOPure value) = unary fuel globals "pure" value
  generate (S fuel) globals (WriteLine text) = unary fuel globals "write" text
  generate (S fuel) globals (IOBind _ _ action continuation) = binary fuel globals "bind" action continuation
  generate (S fuel) globals (Prim WordTypeOp []) = Right (node "erased" [])
  generate (S fuel) globals (Prim (WordLitOp value) []) =
    if value < 0 || value >= wordModulus then Left "JavaScript Word literal out of range"
    else Right (node "word" [jsonString (show value)])
  generate (S fuel) globals (Prim WordFromNatOp [x]) = unary fuel globals "wordFromNat" x
  generate (S fuel) globals (Prim WordToStringOp [x]) = unary fuel globals "wordToString" x
  generate (S fuel) globals (Prim BytesEqualOp [a,b]) = binary fuel globals "bytesEqual" a b
  generate (S fuel) globals (Prim op [a,b]) = do
    name <- maybe (Left "Unsupported JavaScript primitive") Right (wordOperation op)
    binary fuel globals name a b
  generate (S fuel) globals (Universe _) = Right (node "erased" [])
  generate (S fuel) globals UnitType = Right (node "erased" [])
  generate (S fuel) globals BoolType = Right (node "erased" [])
  generate (S fuel) globals NatType = Right (node "erased" [])
  generate (S fuel) globals StringType = Right (node "erased" [])
  generate (S fuel) globals BytesType = Right (node "erased" [])
  generate (S fuel) globals (DataType _) = Right (node "erased" [])
  generate (S fuel) globals (RecType _) = Right (node "erased" [])
  generate (S fuel) globals (SeqType _ _) = Right (node "erased" [])
  generate (S fuel) globals (IOType _) = Right (node "erased" [])
  generate (S fuel) globals (Pi _ _ _) = Right (node "erased" [])
  generate (S fuel) globals (Sigma _ _ _ _) = Right (node "erased" [])
  generate (S fuel) globals (BoxType _ _) = Right (node "erased" [])
  generate (S fuel) globals (NominalType _ _ _) = Right (node "erased" [])
  generate (S fuel) globals (VariantType _) = Right (node "erased" [])
  generate (S fuel) globals _ = Left "Unsupported JavaScript computational construct"

  generateBranches : Nat -> RuntimeGlobals -> List (Term n) -> Either String (List String)
  generateBranches fuel globals [] = Right []
  generateBranches fuel globals (term :: rest) = do
    code <- generate fuel globals term
    following <- generateBranches fuel globals rest
    Right (code :: following)

  unary : Nat -> RuntimeGlobals -> String -> Term n -> Either String String
  unary fuel globals name a = do
    code <- generate fuel globals a
    Right (node name [code])

  binary : Nat -> RuntimeGlobals -> String -> Term n -> Term n -> Either String String
  binary fuel globals name a b = do
    x <- generate fuel globals a
    y <- generate fuel globals b
    Right (node name [x,y])

  ternary : Nat -> RuntimeGlobals -> String -> Term n -> Term n -> Term n -> Either String String
  ternary fuel globals name a b c = do
    x <- generate fuel globals a
    y <- generate fuel globals b
    z <- generate fuel globals c
    Right (node name [x,y,z])

generateGlobals : RuntimeGlobals -> List GlobalDeclaration -> Either String (List (String,String))
generateGlobals globals [] = Right []
generateGlobals globals ((key,q,ty,body) :: rest) = do
  code <- if q == Erased then Right (node "erased" []) else generate 1024 globals body
  following <- generateGlobals globals rest
  Right ((show key,code) :: following)

nodeEntry : String
nodeEntry = "\nexport function run(host, options = {}) { return runProgram(fibrilProgram, host, options); }\n" ++
  "if (typeof process !== 'undefined' && process.versions?.node && process.argv[1]) {\n" ++
  " const {pathToFileURL} = await import('node:url');\n" ++
  " const {realpathSync} = await import('node:fs');\n" ++
  " let direct=false; try { direct=import.meta.url===pathToFileURL(process.argv[1]).href || import.meta.url===pathToFileURL(realpathSync(process.argv[1])).href; } catch {}\n" ++
  " if (direct) {\n" ++
  "  try { const {writeSync} = await import('node:fs'); run({write(bytes) { let i=0; while(i<bytes.length) {const n=writeSync(1,bytes,i,bytes.length-i);if(n<=0)throw new Error('stdout write failed');i+=n;}},flush() {}}); }\n" ++
  "  catch(error) { process.stderr.write('fibril javascript: '+error.message+'\\n'); process.exitCode=1; }\n" ++
  " }\n}\n"

public export
emitCheckedJSGlobals : RuntimeGlobals -> Term 0 -> Either String String
emitCheckedJSGlobals globals term = do
  declarations <- reachableGlobals globals term
  let syntax : List (Term 0) = term :: concatMap (\(_,_,ty,body) => [ty,body]) declarations
  if not (all (supported . maskGlobalRefs) syntax)
    then Left "JavaScript backend rejects input, binary IO, file handles and regions, including erased/dead syntax" else Right ()
  case checkRuntimeGlobals globals checkingDepth typeReductionFuel Empty term (IOType UnitType) of
    Left err => Left ("JavaScript entry checking: " ++ show err)
    Right _ => Right ()
  if sharedProgramNodes term declarations > 8192 then Left "JavaScript core admission exceeds 8192 nodes" else Right ()
  if sharedProgramPayload term declarations > payloadLimit then Left "JavaScript literal admission exceeds 8192 characters" else Right ()
  globalsCode <- generateGlobals globals declarations
  entry <- generate 1024 globals term
  Right ("// Generated from checked Fibril core; experimental output-only ES module.\n" ++ runtimeSource ++
    "\nconst fibrilProgram = " ++ jsonObject [("entry",entry),("globals",jsonObject globalsCode)] ++ ";\n" ++ nodeEntry)

public export
emitCheckedJS : Term 0 -> Either String String
emitCheckedJS = emitCheckedJSGlobals emptyRuntimeGlobals
