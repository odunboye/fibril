-- Canonical dependent motives for the explicit unary/binary record fragment.
-- These are untrusted term builders, not new kernel projection/eta rules.
module Fibril.Elaboration.Expression.Motive

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Source.Text
import Fibril.Source.Resolve.Error
import Fibril.Elaboration.Expression.Scope

%default total

boxField : Quantity -> Term n -> Term n -> Term n
boxField q domain value =
  BoxCase (Lambda Erased (BoxType q domain) (weaken domain)) value
    (Lambda q domain (Variable FZ))

firstField : Quantity -> Quantity -> Term n -> Term (S n) -> Term n -> Term n
firstField q r domain second value =
  PairCase (Lambda Erased (Sigma q r domain second) (weaken domain)) value
    (Lambda q domain (Lambda r second (Variable (FS FZ))))

secondField : Quantity -> Quantity -> Term n -> Term (S n) -> Term n -> Term n
secondField q r domain second value =
  let liftedSecond = rename (liftRenaming FS) second
      extracted = firstField q r (weaken domain) liftedSecond (Variable FZ)
      result = instantiateTerm extracted liftedSecond
   in PairCase (Lambda Erased (Sigma q r domain second) result) value
        (Lambda q domain (Lambda r second (Variable FZ)))

admit : Position -> Nat -> Either ResolveError ()
admit position size =
  if size > inferredResultNodes
     then Left (CannotElaborate position "Inferred dependent motive exceeds 512 nodes; use an explicit return motive")
     else Right ()

checkedSubstitution : Position -> Nat -> (Fin n -> Term m) -> Term n -> Either ResolveError (Term m)
checkedSubstitution position estimate env result = do
  admit position estimate
  let body = substituteTerm env result
  if typeNodes body > estimate
     then Left (CannotElaborate position "Internal dependent motive expansion estimate was insufficient")
     else Right body

public export
unaryMotive : Position -> Quantity -> Term n -> Term (S n) -> Either ResolveError (Term n)
unaryMotive position q domain result = case dropNewest result of
  Just outer => Right (Lambda Erased (BoxType q domain) (weaken outer))
  Nothing => do
    let fieldSize = 6 + 3 * typeNodes domain
    let weights : Fin (S n) -> Nat
        weights FZ = fieldSize
        weights (FS _) = 1
    let replace : Fin (S n) -> Term (S n)
        replace FZ = boxField q (weaken domain) (Variable FZ)
        replace (FS outer) = Variable (FS outer)
    body <- checkedSubstitution position (substitutionNodes weights result) replace result
    Right (Lambda Erased (BoxType q domain) body)

public export
binaryMotive : Position -> Quantity -> Quantity -> Term n -> Term (S n) ->
               Term (S (S n)) -> Either ResolveError (Term n)
binaryMotive position q r domain second result = case dropNewest result >>= dropNewest of
  Just outer => Right (Lambda Erased (Sigma q r domain second) (weaken outer))
  Nothing => do
    let a = typeNodes domain
    let b = typeNodes second
    let firstSize = 7 + 3 * a + 2 * b
    let firstWeights : Fin (S n) -> Nat
        firstWeights FZ = firstSize
        firstWeights (FS _) = 1
    let dependentTypeSize = substitutionNodes firstWeights second
    let secondSize = 7 + 2 * a + 2 * b + dependentTypeSize
    let weights : Fin (S (S n)) -> Nat
        weights FZ = secondSize
        weights (FS FZ) = firstSize
        weights (FS (FS _)) = 1
    let replace : Fin (S (S n)) -> Term (S n)
        replace FZ = secondField q r (weaken domain) (rename (liftRenaming FS) second) (Variable FZ)
        replace (FS FZ) = firstField q r (weaken domain) (rename (liftRenaming FS) second) (Variable FZ)
        replace (FS (FS outer)) = Variable (FS outer)
    body <- checkedSubstitution position (substitutionNodes weights result) replace result
    Right (Lambda Erased (Sigma q r domain second) body)
