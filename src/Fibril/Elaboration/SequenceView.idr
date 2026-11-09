-- Small, untrusted, semantics-preserving views of checked eta helpers.
-- No arbitrary beta-normalization of recursive bodies is performed here.
module Fibril.Elaboration.SequenceView

import Data.Fin
import Data.List
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Erased

%default total

argumentsInOrder : Nat -> List (Term n) -> Bool
argumentsInOrder Z [] = True
argumentsInOrder (S count) (Variable i :: rest) = finToNat i == count && argumentsInOrder count rest
argumentsInOrder _ _ = False

typeFormer : Nat -> Term n -> Bool
typeFormer count (Lambda Erased _ body) = typeFormer (S count) body
typeFormer count (SeqType _ (Variable FZ)) = count == 1
typeFormer count body = case dataTypeSpine body of
  Just (_, args) => argumentsInOrder count args
  Nothing => False

applyFormer : Term n -> List (Term n) -> Maybe (Term n)
applyFormer (Lambda Erased _ body) (argument :: rest) = applyFormer (instantiateTerm argument body) rest
applyFormer body [] = Just body
applyFormer _ _ = Nothing

-- Only exact eta type formers are expanded, preserving every actual argument
-- once. Thus calls in type arguments are not lost to the termination analysis.
public export
familyAnnotation : GlobalContext -> Term n -> Maybe (Term n)
familyAnnotation globals term = collect 8 term []
  where
    collect : Nat -> Term m -> List (Term m) -> Maybe (Term m)
    collect Z _ _ = Nothing
    collect (S fuel) (Apply fn arg) args = collect fuel fn (arg :: args)
    collect (S fuel) (GlobalRef key) args = do
      (Erased, _, body) <- globalEntry globals key | _ => Nothing
      if typeFormer 0 body then applyFormer (rename absurd body) args else Nothing
    collect _ _ _ = Nothing

foldHelper : Term n -> Bool
foldHelper (Lambda Erased (Universe 0) (Lambda Erased _ (Lambda Linear _ (Lambda Unrestricted _ (Lambda Linear _
    (SeqFold (Variable (FS (FS (FS FZ)))) (Variable (FS (FS FZ))) (Variable (FS FZ)) (Variable FZ))))))) = True
foldHelper _ = False

public export
sequenceApplication : GlobalContext -> Term n -> Maybe (Term n)
sequenceApplication globals term = collect 5 term []
  where
    collect : Nat -> Term m -> List (Term m) -> Maybe (Term m)
    collect (S fuel) (Apply fn arg) args = collect fuel fn (arg :: args)
    collect fuel (GlobalRef key) [element, motive, base, step, value] = do
      (Unrestricted, _, body) <- globalEntry globals key | _ => Nothing
      if foldHelper body then
        -- Preserve the erased type argument, including its logical calls.
        Just (Apply (Lambda Erased (Universe 0)
          (SeqFold (weaken motive) (weaken base) (weaken step) (weaken value))) element)
        else Nothing
    collect _ _ _ = Nothing
