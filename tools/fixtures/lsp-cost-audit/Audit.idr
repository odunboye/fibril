module Audit

import System
import Data.Fin
import Data.List
import Fibril.Driver.ModuleCheck
import Fibril.Driver.ModuleGraph
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Quantity
import Fibril.Core.Erased
import Fibril.Core.WeakHead
import Fibril.Core.Size
import Fibril.Data.Bytes
import Fibril.Elaboration.Expression.Payload

%default covering

-- OFFLINE syntax inventory. Uses existing erased inference to identify Apply
-- quantities, not a new erasure semantics or an admission transformation.
applicationRole : {n : Nat} -> Context n -> Term n -> String
applicationRole context fun = case inferErased 512 128 context fun of
  Left _ => "unknown_argument"
  Right ty => case weakHead 128 ty of
    HeadForm (Pi Erased _ _) => "erased_argument"
    HeadForm (Pi _ _ _) => "computational"
    _ => "unknown_argument"

fieldRole : Term n -> Nat -> String
fieldRole annotation field = case weakHead 128 annotation of
  HeadForm (Sigma q r _ _) => if (if field == 0 then q else r) == Erased then "erased_field" else "computational"
  HeadForm (BoxType q _) => if q == Erased then "erased_field" else "computational"
  HeadForm (VariantType arms) => case variantAt field arms of
    Just (Just (Erased, _)) => "erased_field"
    Just _ => "computational"
    _ => "unknown_field"
  _ => "unknown_field"

quantityCode : Quantity -> Nat
quantityCode Erased = 0
quantityCode Linear = 1
quantityCode Unrestricted = 2

textCodes : String -> List Nat
textCodes value = map (cast . ord) (unpack value)

node : String -> String -> List Nat -> Nat -> Nat -> List String -> String
node tag role detail literal nominal children =
  "{\"tag\":" ++ show tag ++ ",\"role\":" ++ show role ++
  ",\"detail\":" ++ show detail ++ ",\"literal\":" ++ show literal ++ ",\"nominal\":" ++ show nominal ++
  ",\"children\":[" ++ concat (intersperse "," children) ++ "]}"

mutual
  dump : {n : Nat} -> Context n -> String -> Term n -> String
  dump context role (Variable index) = node "Variable" role [finToNat index] (0) (0) ([])
  dump context role (Universe level) = node "Universe" "metadata" [level] (0) (0) ([])
  dump context role UnitType = node "UnitType" "metadata" [] (0) (0) ([])
  dump context role UnitValue = node "UnitValue" role [] (0) (0) ([])
  dump context role BoolType = node "BoolType" "metadata" [] (0) (0) ([])
  dump context role BoolTrue = node "BoolTrue" role [] (0) (0) ([])
  dump context role BoolFalse = node "BoolFalse" role [] (0) (0) ([])
  dump context role NatType = node "NatType" "metadata" [] (0) (0) ([])
  dump context role NatZero = node "NatZero" role [] (0) (0) ([])
  dump context role (NatSucc x) = node "NatSucc" role [] (0) (0) ([dump context "computational" x])
  dump context role (NatRec p z s x) = node "NatRec" role [] (0) (0) ([dump context "metadata" p] ++ [dump context "computational" z] ++ [dump context "computational" s] ++ [dump context "computational" x])
  dump context role (NatRecRuntime p z s x) = node "NatRecRuntime" role [] (0) (0) ([dump context "metadata" p] ++ [dump context "computational" z] ++ [dump context "computational" s] ++ [dump context "computational" x])
  dump context role (RecType value) = node "RecType" "metadata" (textCodes value) (0) (length value) ([])
  dump context role (RecEnd ty) = node "RecEnd" role [] (0) (0) ([dump context "metadata" ty])
  dump context role (RecMore ty x) = node "RecMore" role [] (0) (0) ([dump context "metadata" ty] ++ [dump context "computational" x])
  dump context role (RecFold p z s x) = node "RecFold" role [] (0) (0) ([dump context "metadata" p] ++ [dump context "computational" z] ++ [dump context "computational" s] ++ [dump context "computational" x])
  dump context role (RecCase p x z s) = node "RecCase" role [] (0) (0) ([dump context "metadata" p] ++ [dump context "computational" x] ++ [dump context "computational" z] ++ [dump context "computational" s])
  dump context role (NatCase p x z s) = node "NatCase" role [] (0) (0) ([dump context "metadata" p] ++ [dump context "computational" x] ++ [dump context "computational" z] ++ [dump context "computational" s])
  dump context role (SeqCase p x z s) = node "SeqCase" role [] (0) (0) ([dump context "metadata" p] ++ [dump context "computational" x] ++ [dump context "computational" z] ++ [dump context "computational" s])
  dump context role (SeqType key a) = node "SeqType" "metadata" (textCodes key) (0) (length key) ([dump context "computational" a])
  dump context role (SeqNil ty) = node "SeqNil" role [] (0) (0) ([dump context "metadata" ty])
  dump context role (SeqCons ty h t) = node "SeqCons" role [] (0) (0) ([dump context "metadata" ty] ++ [dump context "computational" h] ++ [dump context "computational" t])
  dump context role (SeqFold p z s x) = node "SeqFold" role [] (0) (0) ([dump context "metadata" p] ++ [dump context "computational" z] ++ [dump context "computational" s] ++ [dump context "computational" x])
  dump context role (IterateBinary stateType resultType count step initial) = node "IterateBinary" role [] (0) (0) ([dump context "metadata" stateType] ++ [dump context "metadata" resultType] ++ [dump context "computational" count] ++ [dump context "computational" step] ++ [dump context "computational" initial])
  dump context role (ReadBytes x) = node "ReadBytes" role [] (0) (0) ([dump context "computational" x])
  dump context role (WriteBytes x) = node "WriteBytes" role [] (0) (0) ([dump context "computational" x])
  dump context role RejectBytes = node "RejectBytes" role [] (0) (0) ([])
  dump context role FlushBytes = node "FlushBytes" role [] (0) (0) ([])
  dump context role ReadLine = node "ReadLine" role [] (0) (0) ([])
  dump context role (FileHandleValue identity generation) = node "FileHandleValue" role [identity, generation] (0) (0) ([])
  dump context role (ReadInputFile handle) = node "ReadInputFile" role [] (0) (0) ([dump context "computational" handle])
  dump context role (BytesLengthIs a b) = node "BytesLengthIs" role [] (0) (0) ([dump context "computational" a] ++ [dump context "computational" b])
  dump context role (BytesIndex a b) = node "BytesIndex" role [] (0) (0) ([dump context "computational" a] ++ [dump context "computational" b])
  dump context role (BytesSlice a b c) = node "BytesSlice" role [] (0) (0) ([dump context "computational" a] ++ [dump context "computational" b] ++ [dump context "computational" c])
  dump context role (UTF8Encode x) = node "UTF8Encode" role [] (0) (0) ([dump context "computational" x])
  dump context role (UTF8Decode x) = node "UTF8Decode" role [] (0) (0) ([dump context "computational" x])
  dump context role BytesType = node "BytesType" "metadata" [] (0) (0) ([])
  dump context role (BytesValue value) = node "BytesValue" role (map cast (Fibril.Data.Bytes.toList value)) (byteLength value) (0) ([])
  dump context role (BytesShare x) = node "BytesShare" role [] (0) (0) ([dump context "computational" x])
  dump context role (BytesLength x) = node "BytesLength" role [] (0) (0) ([dump context "computational" x])
  dump context role (BytesOctet x) = node "BytesOctet" role [] (0) (0) ([dump context "computational" x])
  dump context role (BytesAppend a b) = node "BytesAppend" role [] (0) (0) ([dump context "computational" a] ++ [dump context "computational" b])
  dump context role StringType = node "StringType" "metadata" [] (0) (0) ([])
  dump context role (StringValue value) = node "StringValue" role (textCodes value) (length value) (0) ([])
  dump context role (StringAppend a b) = node "StringAppend" role [] (0) (0) ([dump context "computational" a] ++ [dump context "computational" b])
  dump context role (StringEqual a b) = node "StringEqual" role [] (0) (0) ([dump context "computational" a] ++ [dump context "computational" b])
  dump context role (NominalType key indices shape) = node "NominalType" "metadata" (textCodes key) (0) (length key) (terms context "computational" indices ++ [dump context "computational" shape])
  dump context role (NominalValue ty value) = node "NominalValue" role [] (0) (0) ([dump context "metadata" ty] ++ [dump context "computational" value])
  dump context role (NominalCase motive value branch) = node "NominalCase" role [] (0) (0) ([dump context "metadata" motive] ++ [dump context "computational" value] ++ [dump context "computational" branch])
  dump context role (VariantType descriptors) = node "VariantType" "metadata" [] (0) (0) (arms context "computational" descriptors)
  dump context role (VariantValue ty index Nothing) = node "VariantValue" role [index] (0) (0) ([dump context "metadata" ty])
  dump context role (VariantValue ty index (Just value)) = node "VariantValue" role [index] (0) (0) ([dump context "metadata" ty] ++ [dump context (fieldRole ty index) value])
  dump context role (VariantCase motive value branches) = node "VariantCase" role [] (0) (0) ([dump context "metadata" motive] ++ [dump context "computational" value] ++ terms context "computational" branches)
  dump context role (BoxType q a) = node "BoxType" "metadata" [quantityCode q] (0) (0) ([dump context "computational" a])
  dump context role (BoxValue a b) = node "BoxValue" role [] (0) (0) ([dump context "metadata" a] ++ [dump context (fieldRole a 0) b])
  dump context role (BoxCase a b c) = node "BoxCase" role [] (0) (0) ([dump context "metadata" a] ++ [dump context "computational" b] ++ [dump context "computational" c])
  dump context role (WithInputFile result path body) = node "WithInputFile" role [] (0) (0) ([dump context "metadata" result] ++ [dump context "computational" path] ++ [dump context "computational" body])
  dump context role (IOType a) = node "IOType" "metadata" [] (0) (0) ([dump context "computational" a])
  dump context role (FileHandleType region) = node "FileHandleType" "metadata" [] (0) (0) ([dump context "computational" region])
  dump context role (IOPure a) = node "IOPure" role [] (0) (0) ([dump context "computational" a])
  dump context role (WriteLine a) = node "WriteLine" role [] (0) (0) ([dump context "computational" a])
  dump context role (IOBind a b c d) = node "IOBind" role [] (0) (0) ([dump context "metadata" a] ++ [dump context "metadata" b] ++ [dump context "computational" c] ++ [dump context "computational" d])
  dump context role (BoolCase a b c) = node "BoolCase" role [] (0) (0) ([dump context "computational" a] ++ [dump context "computational" b] ++ [dump context "computational" c])
  dump context role (Sigma q r a b) = node "Sigma" "metadata" [quantityCode q, quantityCode r] (0) (0) ([dump context "metadata" a] ++ [dump (Extend context q a) "metadata" b])
  dump context role (PairCase motive value branch) = node "PairCase" role [] (0) (0) ([dump context "metadata" motive] ++ [dump context "computational" value] ++ [dump context "computational" branch])
  dump context role (PairValue ty a b) = node "PairValue" role [] (0) (0) ([dump context "metadata" ty] ++ [dump context (fieldRole ty 0) a] ++ [dump context (fieldRole ty 1) b])
  dump context role (Pi q a b) = node "Pi" "metadata" [quantityCode q] (0) (0) ([dump context "metadata" a] ++ [dump (Extend context q a) "metadata" b])
  dump context role (Lambda q a b) = node "Lambda" role [quantityCode q] (0) (0) ([dump context "metadata" a] ++ [dump (Extend context q a) "computational" b])
  dump context role (Apply a b) = node "Apply" role [] (0) (0) ([dump context "computational" a] ++ [dump context (applicationRole context a) b])
  dump context role (UnitCase a b) = node "UnitCase" role [] (0) (0) ([dump context "computational" a] ++ [dump context "computational" b])

  terms : {n : Nat} -> Context n -> String -> List (Term n) -> List String
  terms context role [] = []
  terms context role (x :: xs) = node "ListCell" role [] 0 0 [dump context role x] :: terms context role xs

  arms : {n : Nat} -> Context n -> String -> List (Maybe (Quantity, Term n)) -> List String
  arms context role [] = []
  arms context role (Nothing :: xs) = node "ListCell" role [0] 0 0 [] :: arms context role xs
  arms context role (Just (q, ty) :: xs) = node "ListCell" role [1, quantityCode q] 0 0 [dump context "metadata" ty] :: arms context role xs

inventory : Term 0 -> String
inventory term =
  "{\"core_nodes\":" ++ show (coreNodes term) ++
  ",\"payload_estimate\":" ++ show (payloadSize term) ++
  ",\"tree\":" ++ dump Empty "computational" term ++ "}"

-- NatCase itself binds nothing; its successor function carries its own quantity
-- and Lambda extends the context. The inner erased application needs that context.
natCaseRegression : Quantity -> Term 0
natCaseRegression quantity =
  NatCase (Lambda Erased NatType NatType) (NatSucc NatZero)
    (Apply (Lambda Erased NatType NatZero) NatZero)
    (Lambda quantity NatType
      (Apply (Lambda Erased NatType (Variable (FS FZ))) (Variable FZ)))

main : IO ()
main = do
  args <- getArgs
  case args of
    [_, "--nat-case-regression"] => do
      putStrLn (inventory (natCaseRegression Linear))
      putStrLn (inventory (natCaseRegression Unrestricted))
    [_, root, entry] => do
      checked <- checkProject root entry
      case checked of
        Left err => die (renderGraphError err)
        Right project => putStrLn (inventory project.term)
    _ => die "usage: audit ROOT ENTRY | audit --nat-case-regression"
