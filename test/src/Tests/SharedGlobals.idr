module Tests.SharedGlobals

import Data.Fin
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Term
import Fibril.Core.SharedProgram
import Fibril.Core.Size
import Fibril.Core.Quantity
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.ResourceAdmission
import Fibril.Core.EffectAdmission

%default total

isLeft : Either e a -> Bool
isLeft (Left _) = True
isLeft _ = False

isRight : Either e a -> Bool
isRight (Right _) = True
isRight _ = False

normalIs : ReductionResult n -> Term n -> Bool
normalIs (Normal value) expected = sameSyntax value expected
normalIs _ _ = False

identityType : Term 0
identityType = Pi Linear NatType NatType

identity : Term 0
identity = Lambda Linear NatType (Variable FZ)

base : Either RuntimeError RuntimeGlobals
base = extendRuntimeGlobals 512 128 emptyRuntimeGlobals 0 Unrestricted identityType identity

withBase : (RuntimeGlobals -> Bool) -> Bool
withBase predicate = case base of
  Left _ => False
  Right globals => predicate globals

-- Each body is a five-node term referencing an earlier declaration twice.
-- Inlining this chain would construct an exponential tree before checking.
chain : Nat -> Nat -> RuntimeGlobals -> Either RuntimeError RuntimeGlobals
chain Z next globals = Right globals
chain (S rest) next globals = do
  extended <- extendRuntimeGlobals 512 128 globals (S next) Unrestricted NatType
    (BoolCase BoolTrue (GlobalRef next) (GlobalRef next))
  chain rest (S next) extended

sharedChain : Either RuntimeError RuntimeGlobals
sharedChain = do
  zero <- extendRuntimeGlobals 512 128 emptyRuntimeGlobals 0 Unrestricted NatType NatZero
  chain 64 0 zero

export
checks : List (String, Bool)
checks =
  [ ("raw global references cannot forge a type",
      isLeft (inferErased 512 128 Empty (the (Term 0) (GlobalRef 0))))
  , ("raw global references cannot authorize execution",
      isLeft (inferRuntime 512 128 Empty (the (Term 0) (GlobalRef 0))))
  , ("shared globals independently check their declared type and body",
      isLeft (extendRuntimeGlobals 512 128 emptyRuntimeGlobals 0 Unrestricted NatType BoolTrue))
  , ("shared global signatures must themselves be types",
      isLeft (extendRuntimeGlobals 512 128 emptyRuntimeGlobals 0 Unrestricted NatZero NatZero))
  , ("shared globals reject self references",
      isLeft (extendRuntimeGlobals 512 128 emptyRuntimeGlobals 0 Unrestricted NatType (GlobalRef 0)))
  , ("shared globals reject forward references",
      isLeft (extendRuntimeGlobals 512 128 emptyRuntimeGlobals 0 Unrestricted NatType (GlobalRef 1)))
  , ("shared globals reject linear global ownership",
      isLeft (extendRuntimeGlobals 512 128 emptyRuntimeGlobals 0 Linear NatType NatZero))
  , ("shared globals reject duplicate identities",
      withBase (\globals => isLeft (extendRuntimeGlobals 512 128 globals 0 Unrestricted NatType NatZero)))
  , ("shared globals check runtime binder quantities before admission",
      isLeft (extendRuntimeGlobals 512 128 emptyRuntimeGlobals 0 Unrestricted identityType (Lambda Linear NatType NatZero)))
  , ("checked references infer the independently checked signature",
      withBase (\globals => case inferRuntimeGlobals globals 512 128 Empty (the (Term 0) (GlobalRef 0)) of
        Right result => sameSyntax result.inferredType identityType
        Left _ => False))
  , ("global applications use ordinary runtime quantity checking",
      withBase (\globals => isRight (checkRuntimeGlobals globals 512 128 Empty (Apply (GlobalRef 0) NatZero) NatType)))
  , ("global unfolding and beta contraction each spend conversion fuel",
      withBase (\globals => normalIs (normalizeGlobals (globalValue (erasedGlobals globals)) 2 (the (Term 0) (Apply (GlobalRef 0) NatZero))) NatZero))
  , ("global unfolding cannot silently succeed on exhausted conversion",
      withBase (\globals => case normalizeGlobals (globalValue (erasedGlobals globals)) 0 (the (Term 0) (GlobalRef 0)) of
        OutOfFuel _ => True
        _ => False))
  , ("weak head unfolds a checked global to expose its shape",
      withBase (\globals => case weakHeadGlobals (globalValue (erasedGlobals globals)) 1 (the (Term 0) (GlobalRef 0)) of
        HeadForm (Lambda Linear NatType _) => True
        _ => False))
  , ("erased aliases are available to type conversion without runtime authority",
      case extendRuntimeGlobals 512 128 emptyRuntimeGlobals 0 Erased (Universe 0) NatType of
        Left _ => False
        Right globals => isRight (checkErasedGlobals (erasedGlobals globals) 512 128 Empty NatZero (GlobalRef 0)) &&
          isLeft (inferRuntimeGlobals globals 512 128 Empty (the (Term 0) (GlobalRef 0))))
  , ("erased globals can be supplied to erased arguments",
      case extendRuntimeGlobals 512 128 emptyRuntimeGlobals 0 Erased NatType NatZero of
        Left _ => False
        Right globals => isRight (inferRuntimeGlobals globals 512 128 Empty
          (the (Term 0) (Apply (Lambda Erased NatType UnitValue) (GlobalRef 0)))))
  , ("an erased dependency cannot be laundered into an unrestricted global",
      case extendRuntimeGlobals 512 128 emptyRuntimeGlobals 0 Erased NatType NatZero of
        Left _ => False
        Right globals => isLeft (extendRuntimeGlobals 512 128 globals 1 Unrestricted NatType (GlobalRef 0)))
  , ("an earlier closed helper is admitted in a decreasing recursive body",
      withBase (\globals => isRight (inferRuntimeGlobals globals 512 128 Empty
        (Fix identityType (Lambda Linear NatType
          (NatCase (Lambda Erased NatType NatType) (Variable FZ) NatZero
            (Lambda Linear NatType
              (Apply (GlobalRef 0) (Apply (Variable (FS (FS FZ))) (Variable FZ))))))))))
  , ("global-headed results do not establish a recursive decrease",
      withBase (\globals => isLeft (inferRuntimeGlobals globals 512 128 Empty
        (Fix identityType (Lambda Linear NatType
          (Apply (Variable (FS FZ)) (Apply (GlobalRef 0) (Variable FZ))))))))
  , ("shared references survive renaming without capture",
      sameSyntax (rename FS (the (Term 1) (GlobalRef 7))) (the (Term 2) (GlobalRef 7)))
  , ("shared references survive local substitution without capture",
      sameSyntax (substituteTerm (\_ => NatZero) (the (Term 1) (GlobalRef 7))) (the (Term 0) (GlobalRef 7)))
  , ("a reference counts as one syntax node, independently of its body",
      coreNodes (the (Term 0) (GlobalRef 7)) == 1)
  , ("legacy resource admission refuses unresolved global references",
      containsFileReference (the (Term 0) (GlobalRef 0)))
  , ("nominal occurrence scanning cannot hide a family behind a global reference",
      case extendRuntimeGlobals 512 128 emptyRuntimeGlobals 0 Erased (Universe 0)
        (NominalType "Family" [] (VariantType [Nothing])) of
        Left _ => False
        Right globals => case mentionsNominalGlobals (erasedGlobals globals) "Family" (the (Term 0) (GlobalRef 0)) of
          Right True => True
          _ => False)
  , ("legacy nominal occurrence scans conservatively reject unresolved references",
      mentionsNominal "Family" (the (Term 0) (GlobalRef 0)))
  , ("a 64-level repeated-reference program checks without expansion",
      isRight sharedChain)
  , ("shared admission charges each reachable signature and body exactly once",
      case sharedChain of
        Left _ => False
        Right globals => case reachableGlobals globals (the (Term 0) (GlobalRef 64)) of
          Left _ => False
          Right declarations => length declarations == 65 &&
            sharedProgramNodes (the (Term 0) (GlobalRef 64)) declarations == 323)
  , ("a shared repeated-reference program reduces under an explicit budget",
      case sharedChain of
        Left _ => False
        Right globals => normalIs (normalizeGlobals (globalValue (erasedGlobals globals)) 130
          (the (Term 0) (GlobalRef 64))) NatZero)
  ]
