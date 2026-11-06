-- Isolated fuelled reference machine for restricted recursive groups.
-- Not ordinary core evaluation, source admission, conversion or a backend.
module Fibril.Core.RecursiveGroupReference

import Data.Fin
import Data.Vect
import Fibril.Core.Quantity
import Fibril.Core.RecursiveGroup
import Fibril.Core.Term
import Fibril.Termination.GroupCheck
import Fibril.Termination.SizeChange

%default total

||| Values of the restricted Nat/Bool fragment, not general core values.
public export
data Value = Natural Nat | Boolean Bool

public export
Eq Value where
  Natural x == Natural y = x == y
  Boolean x == Boolean y = x == y
  _ == _ = False

||| Exhaustion never returns a partial success. Certificate acceptance is only
||| a precondition for this isolated experiment, not recursive core admission.
public export
data Problem = GraphFailure GraphProblem
             | CertificateRejected String
             | CertificateInconclusive String
             | Unsupported String
             | InvalidInput String
             | AdmissionExhausted String
             | OutOfFuel
             | InternalMismatch String

private
data Sort = NatSort | BoolSort

withinNat : Nat -> Nat -> Bool
withinNat Z Z = True
withinNat Z (S _) = False
withinNat (S _) Z = True
withinNat (S fuel) (S value) = withinNat fuel value

-- All signatures are checked afresh. Pure Nat/Bool values may be read once or
-- unrestrictedly; erased argument calling conventions remain unsupported.
referenceSignature : Nat -> Term n -> Either Problem ()
referenceSignature Z NatType = Right ()
referenceSignature Z BoolType = Right ()
referenceSignature Z _ = Left (Unsupported "expected a literal Nat or Bool result")
referenceSignature (S rest) (Pi Linear NatType result) = referenceSignature rest result
referenceSignature (S rest) (Pi Linear BoolType result) = referenceSignature rest result
referenceSignature (S rest) (Pi Unrestricted NatType result) = referenceSignature rest result
referenceSignature (S rest) (Pi Unrestricted BoolType result) = referenceSignature rest result
referenceSignature (S _) _ = Left (Unsupported "reference groups require non-erased literal Nat/Bool parameters")

referenceMembers : (remaining : Vect n Nat) -> Members groupShape remaining -> Either Problem ()
referenceMembers [] NoMembers = Right ()
referenceMembers (arity :: rest) (MoreMembers member following) = do
  referenceSignature arity member.signature
  referenceMembers rest following

-- Values are bounded before execution or construction of a successor.
checkValue : Term n -> Value -> Either Problem ()
checkValue NatType (Natural value) =
  if withinNat 256 value then Right () else Left (AdmissionExhausted "Nat value admission exhausted (256)")
checkValue BoolType (Boolean _) = Right ()
checkValue _ _ = Left (InvalidInput "value does not match the member parameter type")

checkArguments : Vect arity Value -> Term n -> Either Problem Sort
checkArguments [] NatType = Right NatSort
checkArguments [] BoolType = Right BoolSort
checkArguments (value :: values) (Pi Linear domain result) = do
  checkValue domain value
  checkArguments values result
checkArguments (value :: values) (Pi Unrestricted domain result) = do
  checkValue domain value
  checkArguments values result
checkArguments _ _ = Left (Unsupported "member signature is outside the reference fragment")

-- Group checking has admitted only these pure ordinary terms. Each term is
-- bounded by the group's node admission; any unexpected form fails closed.
evalTerm : Vect n Value -> Term n -> Either Problem Value
evalTerm env (Variable position) = Right (Data.Vect.index position env)
evalTerm env NatZero = Right (Natural 0)
evalTerm env (NatSucc value) = do
  Natural current <- evalTerm env value
    | _ => Left (InternalMismatch "Nat successor operand is not Nat")
  if withinNat 255 current then Right (Natural (S current))
    else Left (AdmissionExhausted "Nat value admission exhausted (256)")
evalTerm env BoolTrue = Right (Boolean True)
evalTerm env BoolFalse = Right (Boolean False)
evalTerm _ _ = Left (Unsupported "ordinary term is outside the reference fragment")

evalArgs : Vect n Value -> Vect arity (Term n) -> Either Problem (Vect arity Value)
evalArgs env [] = Right []
evalArgs env (arg :: args) = do
  value <- evalTerm env arg
  values <- evalArgs env args
  Right (value :: values)

-- A fuel unit is charged for each reached Body constructor, including Return
-- and Call. Ordinary-term traversal is separately bounded by group admission.
-- Arguments are in signature order; body locals use the reverse order.
run : Nat -> (group : Group size) -> Body group.arities n -> Vect n Value -> Either Problem Value
run Z _ _ _ = Left OutOfFuel
run (S fuel) group (Return value) env = evalTerm env value
run (S fuel) group (Call target args) env = do
  values <- evalArgs env args
  let member = memberAt group target
  _ <- checkArguments values member.signature
  run fuel group member.body (reverse values)
run (S fuel) group (CaseNat value zero successor) env = do
  Natural current <- evalTerm env value
    | _ => Left (InternalMismatch "Nat case scrutinee is not Nat")
  case current of
    Z => run fuel group zero env
    S predecessor => run fuel group successor (Natural predecessor :: env)
run (S fuel) group (CaseBool value yes no) env = do
  Boolean condition <- evalTerm env value
    | _ => Left (InternalMismatch "Bool case scrutinee is not Bool")
  if condition then run fuel group yes env else run fuel group no env
run (S _) _ (CaseList _ _ _) _ = Left (Unsupported "list cases are not supported")

resultMatches : Sort -> Value -> Bool
resultMatches NatSort (Natural _) = True
resultMatches BoolSort (Boolean _) = True
resultMatches _ _ = False

||| Recheck the exact group, direct graph and certificate on every invocation,
||| then run the selected member on checked values with explicit fuel. The
||| result is rechecked against its entry signature. This experiment provides
||| no source acceptance, dependent conversion, recursive-core semantics,
||| backend correctness, normalization proof or hard time/stack/memory bound.
public export
evaluate : (fuel : Nat) -> (group : Group size) -> (target : Fin size) ->
           Vect (index target group.arities) Value -> List Call -> List Call -> Either Problem Value
evaluate fuel group target values calls certificate = do
  case verifyGroup group calls certificate of
    Left err => Left (GraphFailure err)
    Right GraphAccepted => Right ()
    Right (GraphRejected message) => Left (CertificateRejected message)
    Right (GraphInconclusive message) => Left (CertificateInconclusive message)
  if fuel <= 4096 then Right () else Left (AdmissionExhausted "reference fuel admission exhausted (4096)")
  referenceMembers group.arities group.definitions
  let member = memberAt group target
  resultType <- checkArguments values member.signature
  result <- run fuel group member.body (reverse values)
  if resultMatches resultType result then Right result else Left (InternalMismatch "member result has the wrong type")
