-- Narrow ordinary typing and quantitative checking of raw recursive groups.
-- This is not termination checking, recursive evaluation, or source admission.
module Fibril.Core.RecursiveGroupCheck

import Data.Fin
import Data.Vect
import Fibril.Core.Context
import Fibril.Core.Quantity
import Fibril.Core.RecursiveGroup
import Fibril.Core.Term
import Fibril.Core.Usage

%default total

||| Unsupported syntax and exhausted admissions are not successful checks.
||| Invalid identifies a failed type, arity or usage requirement.
public export
data Problem = Invalid String | Unsupported String | Inconclusive String

private
data Atom = Natural | Boolean

Eq Atom where
  Natural == Natural = True
  Boolean == Boolean = True
  _ == _ = False

atom : Term n -> Maybe Atom
atom NatType = Just Natural
atom BoolType = Just Boolean
atom _ = Nothing

atomTerm : Atom -> Term n
atomTerm Natural = NatType
atomTerm Boolean = BoolType

record Signature (arity : Nat) where
  constructor Parsed
  inputs : Vect arity (Quantity, Atom)
  output : Atom

-- Nondependent literal Nat/Bool telescopes only. Pi domains and result may not
-- contain variables, function types, effects, aliases, or recursive references.
parseSignature : (arity : Nat) -> Term n -> Either Problem (Signature arity)
parseSignature Z ty = case atom ty of
  Just result => Right (Parsed [] result)
  Nothing => Left (Invalid "signature result must be a literal Nat or Bool")
parseSignature (S arity) (Pi quantity domain rest) = do
  argument <- case atom domain of
    Just argument => Right argument
    Nothing => Left (Unsupported "signature parameter must be a literal Nat or Bool")
  Parsed inputs output <- parseSignature arity rest
  Right (Parsed ((quantity, argument) :: inputs) output)
parseSignature (S _) _ = Left (Invalid "signature Pi telescope does not match declared arity")

-- Admission counts the complete allowed body tree and embedded term nodes
-- before typing or constructing usage vectors. Calls have a separate budget.
admitTerm : Nat -> Term n -> Either Problem Nat
admitTerm Z _ = Left (Inconclusive "recursive group node admission exhausted (256)")
admitTerm (S nodes) (Variable _) = Right nodes
admitTerm (S nodes) NatZero = Right nodes
admitTerm (S nodes) (NatSucc value) = admitTerm nodes value
admitTerm (S nodes) BoolTrue = Right nodes
admitTerm (S nodes) BoolFalse = Right nodes
admitTerm (S _) _ = Left (Unsupported "unsupported recursive group term")

admitArgs : Nat -> Vect arity (Term n) -> Either Problem Nat
admitArgs nodes [] = Right nodes
admitArgs nodes (arg :: rest) = do
  remaining <- admitTerm nodes arg
  admitArgs remaining rest

admitBody : Nat -> Nat -> Body shape n -> Either Problem (Nat, Nat)
admitBody Z _ _ = Left (Inconclusive "recursive group node admission exhausted (256)")
admitBody (S nodes) calls (Return term) = do
  rest <- admitTerm nodes term
  Right (rest, calls)
admitBody (S nodes) Z (Call _ _) = Left (Inconclusive "recursive group call admission exhausted (128)")
admitBody (S nodes) (S calls) (Call _ args) = do
  rest <- admitArgs nodes args
  Right (rest, calls)
admitBody (S nodes) calls (CaseNat value zero successor) = do
  remaining <- admitTerm nodes value
  (remaining, calls) <- admitBody remaining calls zero
  admitBody remaining calls successor
admitBody (S nodes) calls (CaseBool value yes no) = do
  remaining <- admitTerm nodes value
  (remaining, calls) <- admitBody remaining calls yes
  admitBody remaining calls no
admitBody (S _) _ (CaseList _ _ _) = Left (Unsupported "list cases are not yet checked")

admitArities : Vect n Nat -> Either Problem ()
admitArities [] = Right ()
admitArities (arity :: rest) = do
  if arity <= 8 then Right () else Left (Inconclusive "recursive group arity admission exhausted (8)")
  admitArities rest

admitMembers : Nat -> Nat -> Members shape remaining -> Either Problem ()
admitMembers nodes calls NoMembers = Right ()
admitMembers nodes calls (MoreMembers member rest) = do
  (nodes, calls) <- admitBody nodes calls member.body
  admitMembers nodes calls rest

-- Signature parameters are stored oldest-first; Context extends oldest first,
-- so build it from the reversed vector (newest-first).
contextFrom : Vect n (Quantity, Atom) -> Context n
contextFrom [] = Empty
contextFrom ((quantity, ty) :: rest) = Extend (contextFrom rest) quantity (atomTerm ty)

-- Whitelisted terms have no hidden group calls or higher-order expressions.
-- This computes subterm usage without independently demanding that every
-- ambient linear resource be used by that one subterm.
inferTerm : {n : Nat} -> Context n -> Term n -> Either Problem (Atom, Usage n)
inferTerm context (Variable index) = case atom (lookupType index context) of
  Just ty => Right (ty, variableUsage RuntimeMode index)
  Nothing => Left (Invalid "local does not have a literal Nat or Bool type")
inferTerm context NatZero = Right (Natural, zeroUsage)
inferTerm context (NatSucc value) = do
  (ty, usage) <- inferTerm context value
  if ty == Natural then Right (Natural, usage) else Left (Invalid "Nat successor expects Nat")
inferTerm context BoolTrue = Right (Boolean, zeroUsage)
inferTerm context BoolFalse = Right (Boolean, zeroUsage)
inferTerm _ _ = Left (Unsupported "unsupported recursive group term")

checkArgs : {n : Nat} -> Context n -> Vect arity (Quantity, Atom) -> Vect arity (Term n) -> Either Problem (Usage n)
checkArgs context [] [] = Right zeroUsage
checkArgs context ((quantity, expected) :: params) (arg :: args) = do
  (actual, used) <- inferTerm context arg
  if actual == expected then Right () else Left (Invalid "recursive call argument has the wrong type")
  rest <- checkArgs context params args
  Right (combineUsage (scaleUsage quantity used) rest)

-- Group references are explicit Body.Call nodes. The checker reads the target
-- signature from this same group, never from a supplied graph or cached flag.
checkBody : {n : Nat} -> (group : Group size) -> Context n -> Atom -> Body group.arities n -> Either Problem (Usage n)
checkBody group context expected (Return value) = do
  (actual, usage) <- inferTerm context value
  if actual == expected then Right usage else Left (Invalid "return value has the wrong type")
checkBody group context expected (Call target args) = do
  signature <- parseSignature (index target group.arities) (memberAt group target).signature
  if signature.output == expected then Right () else Left (Invalid "recursive call has the wrong result type")
  checkArgs context signature.inputs args
checkBody group context expected (CaseNat value zero successor) = do
  (ty, scrutinee) <- inferTerm context value
  if ty == Natural then Right () else Left (Invalid "Nat case expects Nat")
  if n < 16 then Right () else Left (Inconclusive "recursive group local admission exhausted (16)")
  zeroUsage <- checkBody group context expected zero
  successorUsage <- checkBody group (Extend context Linear NatType) expected successor
  outer <- case discharge RuntimeMode Linear successorUsage of
    Right usage => Right usage
    Left _ => Left (Invalid "Nat predecessor does not satisfy linear usage")
  Right (combineUsage scrutinee (joinUsage zeroUsage outer))
checkBody group context expected (CaseBool value yes no) = do
  (ty, scrutinee) <- inferTerm context value
  if ty == Boolean then Right () else Left (Invalid "Bool case expects Bool")
  yesUsage <- checkBody group context expected yes
  noUsage <- checkBody group context expected no
  Right (combineUsage scrutinee (joinUsage yesUsage noUsage))
checkBody _ _ _ (CaseList _ _ _) = Left (Unsupported "list cases are not yet checked")

-- Check all signatures before any body so forward and mutual calls cannot
-- rely on an unchecked target telescope.
checkSignatures : (remaining : Vect n Nat) -> Members shape remaining -> Either Problem ()
checkSignatures [] NoMembers = Right ()
checkSignatures (arity :: rest) (MoreMembers member following) = do
  _ <- parseSignature arity member.signature
  checkSignatures rest following

checkMembers : (group : Group size) -> (remaining : Vect n Nat) ->
               Members group.arities remaining -> Either Problem ()
checkMembers group [] NoMembers = Right ()
checkMembers group (arity :: rest) (MoreMembers member following) = do
  signature <- parseSignature arity member.signature
  let context = contextFrom (reverse signature.inputs)
  usage <- checkBody group context signature.output member.body
  case validateUsage RuntimeMode context usage of
    Left _ => Left (Invalid "recursive member does not satisfy parameter usage")
    Right () => checkMembers group rest following

within : Nat -> Vect n a -> Bool
within Z [] = True
within Z (_ :: _) = False
within (S _) [] = True
within (S fuel) (_ :: rest) = within fuel rest

||| Independently check literal Nat/Bool group signatures, bodies, exhaustive
||| cases, calls, and runtime quantities in this restricted raw core fragment.
||| Success is not termination evidence and does not admit or execute recursion.
public export
check : (group : Group size) -> Either Problem ()
check group = do
  if within 16 group.arities then Right () else Left (Inconclusive "recursive group member admission exhausted (16)")
  case group.arities of
    [] => Left (Invalid "recursive group must be nonempty")
    _ :: _ => Right ()
  admitArities group.arities
  admitMembers 256 128 group.definitions
  checkSignatures group.arities group.definitions
  checkMembers group group.arities group.definitions
