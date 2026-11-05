-- Closed nominal and fixed-shape recursive kernels; not a declaration registry.
module Tests.Nominal

import Data.Fin
import Data.List
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Elaboration.Expression.Scope
import Fibril.Elaboration.DataCase

%default total

accepts : Either error result -> Bool
accepts (Right _) = True
accepts _ = False

closed : Term 0 -> Term n
closed = rename absurd

shape : Term n
shape = VariantType [Nothing, Just (Linear, StringType)]

tagged : String -> List (Term n) -> Term n
tagged key indices = NominalType key indices shape

value : Term n
value = NominalValue (tagged "Example.Optional" []) (VariantValue shape 1 (Just (StringValue "present")))

constant : Term n -> Term n -> Term n
constant ty result = Lambda Erased ty (weaken result)

recover : Term 0
recover = NominalCase (constant (tagged "Example.Optional" []) StringType) value
  (Lambda Linear shape
    (VariantCase (constant shape StringType) (Variable FZ)
      [StringValue "missing", Lambda Linear StringType (Variable FZ)]))

typeShape : Term 0
typeShape = VariantType [Nothing, Just (Erased, Universe 0)]

typeTag : Term 0
typeTag = NominalType "Example.TypePacket" [] typeShape

family : Term 0
family = Lambda Erased typeTag
  (NominalCase (constant (closed typeTag) (Universe 0)) (Variable FZ)
    (Lambda Linear (closed typeShape)
      (VariantCase (constant (closed typeShape) (Universe 0)) (Variable FZ)
        [StringType, Lambda Erased (Universe 0) (Variable FZ)])))

identityMotive : Term 0
identityMotive = Lambda Erased typeTag
  (Pi Linear (Apply (closed family) (Variable FZ))
    (weaken (Apply (closed family) (Variable FZ))))

dependentIdentity : Term 0
dependentIdentity = NominalCase identityMotive
  (NominalValue typeTag (VariantValue typeShape 1 (Just StringType)))
  (Lambda Linear typeShape
    (VariantCase
      (Lambda Erased (closed typeShape)
        (Apply (closed identityMotive) (NominalValue (closed typeTag) (Variable FZ))))
      (Variable FZ)
      [Lambda Linear StringType (Variable FZ),
       Lambda Erased (Universe 0) (Lambda Linear (Variable FZ) (Variable FZ))]))

recType : Term n
recType = RecType "Example.Chain"

recMotive : Term n
recMotive = Lambda Erased recType StringType

recStep : Term n
recStep = Lambda Erased recType (Lambda Linear StringType (StringAppend (Variable FZ) (StringValue "!")))

recValue : Term n
recValue = RecMore recType (RecMore recType (RecEnd recType))

indexShape : Term n
indexShape = VariantType [Nothing]

indexed : Term n -> Term n
indexed x = NominalType "Example.ChainIndex" [x] indexShape

dependentRecMotive : Term n
dependentRecMotive = Lambda Erased recType (Pi Erased (indexed (Variable FZ)) StringType)

dependentRecBase : Term n
dependentRecBase = Lambda Erased (indexed (RecEnd recType)) (StringValue "base")

dependentRecStep : Term n
dependentRecStep = Lambda Erased recType
  (Lambda Linear (Apply (weaken dependentRecMotive) (Variable FZ))
    (Lambda Erased (indexed (RecMore recType (Variable (FS FZ))))
      (Apply (Variable (FS FZ))
        (NominalValue (indexed (Variable (FS (FS FZ)))) (VariantValue indexShape 0 Nothing)))))

seqType : Term n
seqType = SeqType "Example.Words" StringType

seqMotive : Term n
seqMotive = Lambda Erased seqType StringType

seqStep : Term n
seqStep = Lambda Linear StringType (Lambda Erased seqType (Lambda Linear StringType
  (StringAppend (Variable (FS (FS FZ))) (Variable FZ))))

seqValue : Term n
seqValue = SeqCons seqType (StringValue "a") (SeqCons seqType (StringValue "b") (SeqNil seqType))

sequenceIndex : Term n -> Term n
sequenceIndex x = NominalType "Example.SeqIndex" [x] indexShape

dependentSeqMotive : Term n
dependentSeqMotive = Lambda Erased seqType (Pi Erased (sequenceIndex (Variable FZ)) StringType)

dependentSeqBase : Term n
dependentSeqBase = Lambda Erased (sequenceIndex (SeqNil seqType)) (StringValue "")

dependentSeqStep : Term n
dependentSeqStep = Lambda Linear StringType (Lambda Erased seqType
  (Lambda Linear (Apply (weaken (weaken dependentSeqMotive)) (Variable FZ))
    (Lambda Erased (sequenceIndex (SeqCons seqType (Variable (FS (FS FZ))) (Variable (FS FZ))))
      (StringAppend (Variable (FS (FS (FS FZ))))
        (Apply (Variable (FS FZ))
          (NominalValue (sequenceIndex (Variable (FS (FS FZ)))) (VariantValue indexShape 0 Nothing)))))))

public export
checks : List (String, Bool)
checks =
  [ ("recursive one-step case exposes and consumes the linear tail",
      let more = Lambda Linear recType (RecFold recMotive (StringValue "") recStep (Variable FZ))
          candidate = RecCase recMotive recValue (StringValue "end") more in
      accepts (checkRuntime 512 128 Empty candidate StringType) &&
      case normalize 32 candidate of
        Normal result => sameSyntax result (StringValue "!") && accepts (checkRuntime 512 128 Empty result StringType)
        _ => False)
  , ("recursive case joins one-use branch captures",
      let ctx = Extend Empty Linear StringType
          more = Lambda Linear recType (RecFold recMotive (Variable (FS FZ)) recStep (Variable FZ))
          candidate = RecCase recMotive (RecEnd recType) (Variable FZ) more in
      accepts (checkRuntime 512 128 ctx candidate StringType))
  , ("recursive case rejects a dropped tail and a bad inactive branch",
      let dropped = Lambda Linear recType (StringValue "bad")
          wrong = Lambda Linear recType (RecFold recMotive (StringValue "") recStep (Variable FZ)) in
      not (accepts (checkRuntime 512 128 Empty (RecCase recMotive (RecEnd recType) (StringValue "ok") dropped) StringType)) &&
      not (accepts (checkErased 512 128 Empty (RecCase recMotive (RecEnd recType) BoolTrue wrong) StringType)))
  , ("recursive case checks dependent motives on neutral tails",
      let ctx = Extend Empty Linear recType
          tail = Variable FZ
          value = RecMore recType tail
          more = Lambda Linear recType
            (Lambda Erased (indexed (RecMore recType (Variable FZ)))
              (Apply (RecFold dependentRecMotive dependentRecBase dependentRecStep (Variable (FS FZ)))
                (NominalValue (indexed (Variable (FS FZ))) (VariantValue indexShape 0 Nothing))))
          candidate = RecCase dependentRecMotive value dependentRecBase more
          expected = Apply dependentRecMotive value in
      accepts (checkRuntime 512 128 ctx candidate expected) &&
      case step candidate of
        Just reduced => accepts (checkRuntime 512 128 ctx reduced expected)
        Nothing => False)
  , ("sequence one-step case consumes both payloads and contracts",
      let branch = Lambda Linear StringType (Lambda Linear seqType
            (StringAppend (Variable (FS FZ)) (SeqFold seqMotive (StringValue "") seqStep (Variable FZ))))
          candidate = SeqCase seqMotive seqValue (StringValue "empty") branch in
      accepts (checkRuntime 512 128 Empty candidate StringType) &&
      case normalize 64 candidate of
        Normal result => sameSyntax result (StringValue "ab") && accepts (checkRuntime 512 128 Empty result StringType)
        _ => False)
  , ("sequence case joins linear captures and checks inactive branches",
      let ctx = Extend Empty Linear StringType
          branch = Lambda Linear StringType (Lambda Linear seqType
            (StringAppend (Variable (FS FZ)) (SeqFold seqMotive (Variable (FS (FS FZ))) seqStep (Variable FZ))))
          droppedHead = Lambda Linear StringType (Lambda Linear seqType
            (SeqFold seqMotive (StringValue "") seqStep (Variable FZ)))
          droppedTail = Lambda Linear StringType (Lambda Linear seqType (Variable (FS FZ))) in
      accepts (checkRuntime 512 128 ctx (SeqCase seqMotive (SeqNil seqType) (Variable FZ) branch) StringType) &&
      not (accepts (checkRuntime 512 128 Empty (SeqCase seqMotive (SeqNil seqType) (StringValue "") droppedHead) StringType)) &&
      not (accepts (checkRuntime 512 128 Empty (SeqCase seqMotive (SeqNil seqType) (StringValue "") droppedTail) StringType)) &&
      not (accepts (checkErased 512 128 ctx (SeqCase seqMotive (SeqNil seqType) BoolTrue branch) StringType)))
  , ("sequence case dependent motive survives contraction with neutral tail",
      let ctx = Extend Empty Linear seqType
          value = SeqCons seqType (StringValue "a") (Variable FZ)
          branch = Lambda Linear StringType (Lambda Linear seqType
            (Lambda Erased (sequenceIndex (SeqCons seqType (Variable (FS FZ)) (Variable FZ)))
              (StringAppend (Variable (FS (FS FZ)))
                (Apply (SeqFold dependentSeqMotive dependentSeqBase dependentSeqStep (Variable (FS FZ)))
                  (NominalValue (sequenceIndex (Variable (FS FZ))) (VariantValue indexShape 0 Nothing))))))
          candidate = SeqCase dependentSeqMotive value dependentSeqBase branch
          expected = Apply dependentSeqMotive value in
      accepts (checkRuntime 512 128 ctx candidate expected) &&
      case step candidate of
        Just reduced => accepts (checkRuntime 512 128 ctx reduced expected)
        Nothing => False)
  , ("sequence core checks and folds head and tail linearly",
      let candidate = SeqFold seqMotive (StringValue "") seqStep seqValue in
      accepts (checkRuntime 512 128 Empty candidate StringType) &&
      case normalize 64 candidate of
        Normal result => sameSyntax result (StringValue "ab") && accepts (checkRuntime 512 128 Empty result StringType)
        _ => False)
  , ("sequence fold supports dependent motives and a neutral tail",
      let ctx = Extend Empty Linear seqType
          value = SeqCons seqType (StringValue "a") (Variable FZ)
          candidate = SeqFold dependentSeqMotive dependentSeqBase dependentSeqStep value
          expected = Apply dependentSeqMotive value in
      accepts (checkRuntime 512 128 ctx candidate expected) &&
      case step candidate of
        Just reduced => accepts (checkRuntime 512 128 ctx reduced expected)
        Nothing => False)
  , ("sequence identity retains key and element type",
      not (accepts (checkErased 512 128 Empty (SeqNil (SeqType "Example.Other" StringType)) seqType)) &&
      not (accepts (checkErased 512 128 Empty (SeqNil (SeqType "Example.Words" BoolType)) seqType)) &&
      not (accepts (inferErased 512 128 Empty (SeqType "Example.Words" (Universe 0)))))
  , ("sequence constructor rejects wrong payload and tail",
      not (accepts (checkRuntime 512 128 Empty (SeqCons seqType BoolTrue (SeqNil seqType)) seqType)) &&
      not (accepts (checkRuntime 512 128 Empty (SeqCons seqType (StringValue "x") (SeqNil (SeqType "Example.Other" StringType))) seqType)))
  , ("sequence fold requires exactly one induction-result use",
      let dropIH = Lambda Linear StringType (Lambda Erased seqType
            (Lambda Linear StringType (Variable (FS (FS FZ))))) in
      case checkRuntime 512 128 Empty (SeqFold seqMotive (StringValue "") dropIH (SeqNil seqType)) StringType of
        Left (BoundUsage Linear Erased) => True
        _ => False)
  , ("sequence fold rejects discarded head and linear capture",
      let dropHead = Lambda Linear StringType (Lambda Erased seqType (Lambda Linear StringType (Variable FZ)))
          captured = Lambda Linear StringType (Lambda Erased seqType (Lambda Linear StringType
            (StringAppend (Variable (FS (FS (FS FZ)))) (StringAppend (Variable (FS (FS FZ))) (Variable FZ))))) in
      not (accepts (checkRuntime 512 128 Empty (SeqFold seqMotive (StringValue "") dropHead (SeqNil seqType)) StringType)) &&
      not (accepts (checkRuntime 512 128 (Extend Empty Linear StringType) (SeqFold seqMotive (StringValue "") captured (SeqNil seqType)) StringType)))
  , ("recursive fixed-shape data checks and structurally folds",
      let candidate = RecFold recMotive (StringValue "base") recStep recValue in
      accepts (checkRuntime 512 128 Empty candidate StringType) &&
      case normalize 32 candidate of
        Normal result => sameSyntax result (StringValue "base!!") && accepts (checkRuntime 512 128 Empty result StringType)
        _ => False)
  , ("recursive fold supports dependent motives and a neutral tail",
      let ctx = Extend Empty Linear recType
          tail = Variable FZ
          value = RecMore recType tail
          candidate = RecFold dependentRecMotive dependentRecBase dependentRecStep value
          expected = Apply dependentRecMotive value in
      accepts (checkRuntime 512 128 ctx candidate expected) &&
      case step candidate of
        Just reduced => accepts (checkRuntime 512 128 ctx reduced expected)
        Nothing => False)
  , ("recursive constructors reject wrong family and wrong annotations",
      not (accepts (checkErased 512 128 Empty (RecEnd StringType) StringType)) &&
      not (accepts (checkErased 512 128 Empty (RecMore recType (RecEnd (RecType "Example.Other"))) recType)))
  , ("recursive fold checks every step even on terminal input",
      not (accepts (checkRuntime 512 128 Empty
        (RecFold recMotive (StringValue "base") (Lambda Erased recType (Lambda Linear StringType (StringValue "discarded"))) (RecEnd recType)) StringType)))
  , ("recursive fold rejects a repeated step capturing a linear resource",
      let ctx = Extend Empty Linear StringType
          captures = Lambda Erased recType (Lambda Linear StringType
            (StringAppend (Variable (FS (FS FZ))) (Variable FZ))) in
      not (accepts (checkRuntime 512 128 ctx (RecFold recMotive (StringValue "base") captures (RecEnd recType)) StringType)))
  , ("assembled direct data case independently checks and reduces",
      let candidate = assembleDataCase (tagged "Example.Optional" []) shape
            (constant (tagged "Example.Optional" []) StringType) value
            [StringValue "missing", Lambda Linear StringType (Variable FZ)]
       in accepts (checkRuntime 512 128 Empty candidate StringType) &&
          case normalize 16 candidate of
            Normal result => sameSyntax result (StringValue "present") && accepts (checkRuntime 512 128 Empty result StringType)
            _ => False)
  , ("assembled dependent motive checks and computes with carried erased type",
      let input = NominalValue typeTag (VariantValue typeShape 1 (Just StringType))
          branch0 = Lambda Linear StringType (Variable FZ)
          branch1 = Lambda Erased (Universe 0) (Lambda Linear (Variable FZ) (Variable FZ))
          candidate = Apply (assembleDataCase typeTag typeShape identityMotive input [branch0, branch1]) (StringValue "dependent")
       in accepts (checkRuntime 512 128 Empty candidate StringType) &&
          case normalize 64 candidate of
            Normal result => sameSyntax result (StringValue "dependent") && accepts (checkRuntime 512 128 Empty result StringType)
            _ => False)
  , ("assembled two-field payload consumes both linear fields and computes",
      let payload = Sigma Linear Linear StringType (weaken StringType)
          choices = VariantType [Nothing, Just (Linear, payload)]
          nominal = NominalType "Example.PairChoice" [] choices
          value = NominalValue nominal (VariantValue choices 1 (Just (PairValue payload (StringValue "hello") (StringValue " world"))))
          motive = constant nominal StringType
          fields = Lambda Linear StringType (Lambda Linear StringType
            (StringAppend (Variable (FS FZ)) (Variable FZ)))
          branch = assemblePairPayloadBranch nominal choices 1 payload motive fields
          candidate = assembleDataCase nominal choices motive value [StringValue "none", branch]
       in accepts (checkRuntime 512 128 Empty candidate StringType) &&
          case normalize 64 candidate of
            Normal result => sameSyntax result (StringValue "hello world") && accepts (checkRuntime 512 128 Empty result StringType)
            _ => False)
  , ("assembled pair payload rejects dropping a linear field or a wrong tag",
      let payload = Sigma Linear Linear StringType (weaken StringType)
          choices = VariantType [Nothing, Just (Linear, payload)]
          nominal = NominalType "Example.PairChoice" [] choices
          value = NominalValue nominal (VariantValue choices 1 (Just (PairValue payload (StringValue "x") (StringValue "y"))))
          motive = constant nominal StringType
          dropped = Lambda Linear StringType (Lambda Linear StringType (Variable FZ))
          both = Lambda Linear StringType (Lambda Linear StringType (StringAppend (Variable (FS FZ)) (Variable FZ)))
       in not (accepts (checkRuntime 512 128 Empty
            (assembleDataCase nominal choices motive value [StringValue "none", assemblePairPayloadBranch nominal choices 1 payload motive dropped]) StringType)) &&
          not (accepts (checkRuntime 512 128 Empty
            (assembleDataCase nominal choices motive value [StringValue "none", assemblePairPayloadBranch nominal choices 0 payload motive both]) StringType)))
  , ("assembled case joins ambient linear demand across alternatives",
      let choices = VariantType [Nothing, Nothing]
          nominal = NominalType "Example.Two" [] choices
          scrutinee = NominalValue nominal (VariantValue choices 0 Nothing)
          motive = constant nominal StringType
          candidate = assembleDataCase nominal choices motive scrutinee [Variable FZ, Variable FZ]
       in accepts (checkRuntime 512 128 (Extend Empty Linear StringType) candidate StringType))
  , ("assembled case rejects branch omission and inconsistent linear capture",
      let choices = VariantType [Nothing, Nothing]
          nominal = NominalType "Example.Two" [] choices
          scrutinee = NominalValue nominal (VariantValue choices 0 Nothing)
          motive = constant nominal StringType
          context = Extend Empty Linear StringType
       in not (accepts (checkRuntime 512 128 context
            (assembleDataCase nominal choices motive scrutinee [Variable FZ]) StringType)) &&
          not (accepts (checkRuntime 512 128 context
            (assembleDataCase nominal choices motive scrutinee [Variable FZ, StringValue "unused"]) StringType)))
  , ("closed nominal type preserves its checked shape universe",
      case inferErased 512 128 Empty typeTag of Right (Universe 1) => True; _ => False)
  , ("nominal constructor and consuming elimination check",
      accepts (checkRuntime 512 128 Empty recover StringType))
  , ("nominal and variant elimination compose without hidden tag padding",
      case normalize 8 recover of Normal result => sameSyntax result (StringValue "present") && accepts (checkRuntime 512 128 Empty result StringType); _ => False)
  , ("different keys with equal shapes are distinct",
      not (accepts (checkRuntime 512 128 Empty value (tagged "Other.Optional" []))))
  , ("phantom parameters remain part of identity",
      not (accepts (checkRuntime 512 128 Empty
        (NominalValue (tagged "Example.Phantom" [StringType]) (VariantValue shape 0 Nothing))
        (tagged "Example.Phantom" [BoolType]))))
  , ("a key does not authorize a substituted shape witness",
      not (accepts (checkErased 512 128 Empty value
        (NominalType "Example.Optional" [] (VariantType [Nothing])))))
  , ("nominal values must check against the exact underlying shape",
      not (accepts (inferRuntime 512 128 Empty
        (NominalValue (tagged "Example.Optional" []) (VariantValue (VariantType [Nothing]) 0 Nothing)))))
  , ("malformed nominal shape and parameters are rejected",
      all (\ty => not (accepts (inferErased 512 128 Empty ty)))
        [NominalType "Bad" [] StringType,
         NominalType "Bad" [] (VariantType []),
         tagged "Bad" [Apply BoolTrue BoolFalse]])
  , ("beta-equivalent parameters give compatible identity",
      accepts (checkRuntime 512 128 Empty
        (NominalValue (tagged "Example.Phantom" [Apply (Lambda Erased (Universe 0) (Variable FZ)) StringType]) (VariantValue shape 0 Nothing))
        (tagged "Example.Phantom" [StringType])))
  , ("erased parameter information is not a runtime capture",
      let ty = tagged "Example.Indexed" [Variable FZ]
       in accepts (checkRuntime 512 128 (Extend Empty Erased BoolType)
         (NominalValue ty (VariantValue shape 0 Nothing)) ty))
  , ("retaining an index in a type does not discharge a linear runtime input",
      let ty = tagged "Example.Indexed" [Variable FZ]
       in not (accepts (checkRuntime 512 128 (Extend Empty Linear BoolType)
         (NominalValue ty (VariantValue shape 0 Nothing)) ty)))
  , ("dependent nominal case recovers identity at an erased carried type",
      accepts (checkRuntime 512 128 Empty (Apply dependentIdentity (StringValue "dependent")) StringType))
  , ("dependent nominal result reduces and independently rechecks",
      case normalize 64 (Apply dependentIdentity (StringValue "dependent")) of
        Normal result => sameSyntax result (StringValue "dependent") && accepts (checkRuntime 512 128 Empty result StringType)
        _ => False)
  , ("nominal case must consume its underlying variant once",
      not (accepts (checkRuntime 512 128 Empty
        (NominalCase (constant (tagged "Example.Optional" []) StringType) value (Lambda Linear shape (StringValue "drop"))) StringType)))
  , ("nominal motives cannot inspect an erased wrapper at runtime",
      not (accepts (checkRuntime 512 128 (Extend Empty Erased (tagged "Example.Optional" []))
        (NominalCase (constant (tagged "Example.Optional" []) shape) (Variable FZ) (Lambda Linear shape (Variable FZ))) shape)))
  , ("nominal motive domain and permission must match",
      not (accepts (inferErased 512 128 Empty
        (NominalCase (constant (tagged "Other.Optional" []) shape) value (Lambda Linear shape (Variable FZ))))))
  , ("nominal elimination is one contraction to application",
      case step recover of Just (Apply _ _) => True; _ => False)
  , ("nominal parameter cells count in size admission",
      typeNodes (the (Term 0) (tagged "Example.Phantom" [StringType])) == 7 &&
      typeNodes (the (Term 0) (tagged "Example.Phantom" (replicate 600 StringType))) == 513)
  , ("partial scope transport retains phantom parameter dependencies",
      case dropNewest (tagged "Example.Phantom" [the (Term 1) (Variable FZ)]) of Nothing => True; _ => False)
  , ("nominal parameter traversal reports checking exhaustion",
      not (accepts (inferErased 16 128 Empty (tagged "Example.Phantom" (replicate 32 StringType)))))
  ]
