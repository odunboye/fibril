module Tests.Word

import Data.Fin
import Data.List
import Data.String
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Size
import Fibril.Elaboration.Expression.Scope
import Fibril.Driver.Check
import Fibril.Driver.Native.Emit

%default total

wordType : Term n
wordType = Prim WordTypeOp []

accepted : Term 0 -> Term 0 -> Bool
accepted term ty = case checkRuntime 1024 128 Empty term ty of
  Left _ => False
  Right _ => True

sourceAccepted : String -> Bool
sourceAccepted source = case checkSource False source of
  Left _ => False
  Right _ => True

normal : Term 0 -> Term 0 -> Bool
normal term expected = case normalize 32 term of
  Normal result => sameSyntax result expected
  _ => False

head : Term 0 -> Term 0 -> Bool
head term expected = case weakHead 32 term of
  HeadForm result => sameSyntax result expected
  _ => False

op : PrimOp -> Integer -> Integer -> Term 0
op o a b = Prim o [wordTerm a, wordTerm b]

openTerms : List (Term 1)
openTerms = [Prim WordAddOp [Variable FZ, wordTerm 1], wordType, wordTerm 7,
             Prim WordLtOp [wordTerm 1, Variable FZ]]

dup : Term 0
dup = Lambda Unrestricted wordType (Prim WordAddOp [Variable FZ, Variable FZ])

public export
checks : List (String, Bool)
checks =
  [("Word type lives in Type 0", either (const False) (const True) (checkErased 64 64 Empty wordType (Universe 0))),
   ("Word literal has type Word", accepted (wordTerm 5) wordType),
   ("maximum Word literal is accepted", accepted (wordTerm 18446744073709551615) wordType),
   ("Word literal beyond 2^64-1 is rejected", not (accepted (wordTerm 18446744073709551616) wordType)),
   ("negative Word literal is rejected", not (accepted (wordTerm (-1)) wordType)),
   ("Word is not Nat", not (accepted (wordTerm 5) NatType) && not (accepted (naturalTerm 5) wordType)),
   ("addition wraps modulo 2^64", normal (op WordAddOp 18446744073709551615 2) (wordTerm 1)),
   ("subtraction wraps below zero", normal (op WordSubOp 0 1) (wordTerm 18446744073709551615)),
   ("multiplication wraps modulo 2^64", normal (op WordMulOp 4294967296 4294967296) (wordTerm 0)),
   ("large product needs no unary expansion", normal (op WordMulOp 1000000007 998244353) (wordTerm 998244359987710471)),
   ("equality yields Bool", normal (op WordEqOp 7 7) BoolTrue && normal (op WordEqOp 7 8) BoolFalse),
   ("comparison is unsigned", normal (op WordLtOp 3 18446744073709551615) BoolTrue && normal (op WordLtOp 18446744073709551615 3) BoolFalse),
   ("head reduction agrees with full reduction", head (op WordAddOp 40 2) (wordTerm 42)),
   ("nested arithmetic reduces operands first", normal (Prim WordAddOp [op WordMulOp 6 7, wordTerm 0]) (wordTerm 42)),
   ("addition result is typed Word", accepted (op WordAddOp 1 2) wordType),
   ("comparison result is typed Bool", accepted (op WordLtOp 1 2) BoolType && not (accepted (op WordLtOp 1 2) wordType)),
   ("operands must both be Word", not (accepted (Prim WordAddOp [wordTerm 1, naturalTerm 2]) wordType) && not (accepted (Prim WordAddOp [StringValue "a", wordTerm 1]) wordType)),
   ("wrong arity is rejected", not (accepted (Prim WordAddOp [wordTerm 1]) wordType) && not (accepted (Prim WordTypeOp [wordTerm 1]) (Universe 0))),
   ("Word values may be duplicated", accepted dup (Pi Unrestricted wordType wordType) && normal (Apply dup (wordTerm 21)) (wordTerm 42)),
   ("Word syntax transports structurally", all (\t => sameSyntax (rename id t) t && sameSyntax (substituteTerm Variable t) t) openTerms),
   ("Word node counts agree with substitution estimator", all (\t => coreNodes t == substitutionNodes (const 1) t) openTerms),
   ("native emission lowers Word arithmetic and comparison", either (const False) (\code => isInfixOf "f_word_lt(" code && isInfixOf "UINT64_C(2)" code) (emitCheckedC (BoolCase (op WordLtOp 1 2) (WriteLine (StringValue "a")) (WriteLine (StringValue "b"))))),
   ("native emission rejects an out-of-range Word literal", either (const True) (const False) (emitCheckedC (BoolCase (op WordLtOp 1 18446744073709551616) (WriteLine (StringValue "a")) (WriteLine (StringValue "b"))))),
   ("source literal arithmetic checks", sourceAccepted "main : Word\nmain = primWordAdd 1w 2w"),
   ("source rejects Word where Nat is expected", not (sourceAccepted "main : Nat\nmain = 5w")),
   ("source rejects literal beyond 2^64-1", not (sourceAccepted "main : Word\nmain = 18446744073709551616w")),
   ("source rejects leading zeros", not (sourceAccepted "main : Word\nmain = 05w")),
   ("source keeps plain numerals as Nat", sourceAccepted "main : Nat\nmain = 5"),
   ("source allows duplicate Word use", sourceAccepted "dbl : (x : Word) -> Word\ndbl x = primWordAdd x x\nmain : Word\nmain = dbl 21w")]
