-- Definitional constructor checking for structural record patterns.
module Fibril.Elaboration.Expression.Constructor

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Reduction
import Fibril.Core.Limits
import Fibril.Core.WeakHead
import Fibril.Elaboration.Expression.Scope
import Fibril.Elaboration.Expression.Conversion
import Fibril.Elaboration.Expression.Payload
import Fibril.Source.Global
import Fibril.Source.Text
import Fibril.Source.Resolve.Error

%default total

public export
inferredFieldNodes : Nat
inferredFieldNodes = 512

||| Compare a checked global against the exact fixed sequence constructors.
||| Its value and all normalization are guarded; no authored schema is trusted.
public export
checkedSequenceConstructorGlobals : GlobalContext -> Position -> Context n -> Term n -> Term n -> GlobalDefinition -> Either ResolveError Nat
checkedSequenceConstructorGlobals shared position ctx ty element definition = do
  if definition.quantity /= Unrestricted then Left (CannotElaborate position "Data-case constructor must be an unrestricted checked global") else Right ()
  closed <- case guardedNormalGlobals shared typeReductionFuel definition.value of
    Nothing => Left (CannotElaborate position "Sequence-case constructor comparison exhausted admission or reduction")
    Just result => Right result
  if 1 + typeNodes closed + typeNodes element > inferredResultNodes ||
     payloadSize closed + payloadSize element > payloadLimit
    then Left (CannotElaborate position "Sequence-case constructor instantiation exceeds admission") else Right ()
  let lifted = rename absurd closed
  candidate <- case closed of
    Lambda Erased domain _ => do
      case checkErasedGlobals shared checkingDepth typeReductionFuel ctx element (rename absurd domain) of
        Left _ => Left (CannotElaborate position "Sequence-case constructor parameter cannot accept the element type")
        Right () => Right ()
      case guardedNormalGlobals shared typeReductionFuel (Apply lifted element) of
        Nothing => Left (CannotElaborate position "Sequence-case constructor instantiation exhausted admission or reduction")
        Just result => Right result
    _ => Right lifted
  if 6 + 2 * typeNodes ty + typeNodes element > inferredResultNodes ||
     2 * payloadSize ty + payloadSize element > payloadLimit
    then Left (CannotElaborate position "Sequence-case canonical constructor exceeds admission") else Right ()
  let nil = SeqNil ty
  let cons = Lambda Linear element (Lambda Linear (weaken ty)
               (SeqCons (weaken (weaken ty)) (Variable (FS FZ)) (Variable FZ)))
  if guardedEqualGlobals shared typeReductionFuel candidate nil then Right 0 else
    if guardedEqualGlobals shared typeReductionFuel candidate cons then Right 1 else
      Left (CannotElaborate position "Sequence-case constructor does not match the scrutinee family and element type, or comparison was inconclusive")

public export
data ConstructorFields : Nat -> Type where
  OneField : Quantity -> Term n -> ConstructorFields n
  TwoFields : Quantity -> Term n -> Quantity -> Term (S n) -> ConstructorFields n

equalGlobals : GlobalContext -> Position -> String -> Term n -> Term n -> Either ResolveError ()
equalGlobals shared position message actual expected = case betaCompareGlobals (globalValue shared) typeReductionFuel actual expected of
  EqualNormalForms => Right ()
  DifferentNormalForms => Left (CannotElaborate position message)
  Inconclusive => Left (CannotElaborate position "Pattern constructor comparison exhausted its reduction budget")

||| The constructor expression is compile-time data, not part of the emitted case.
||| No nominal identity or runtime constructor discrimination is asserted.
public export
checkConstructorGlobals : GlobalContext -> Position -> Nat -> Context n -> Term n -> Term n -> Either ResolveError ()
checkConstructorGlobals shared position arity context constructor branch = do
  ty <- case inferErasedGlobals shared checkingDepth typeReductionFuel context constructor of
    Left err => Left (CannotElaborate position ("Cannot infer pattern constructor type: " ++ show err))
    Right ty => Right ty
  case (arity, branch) of
    (1, Lambda q domain _) => do
      let boxed = BoxType q domain
      equalGlobals shared position "Pattern constructor type does not match the typed fields; instantiate erased parameters explicitly"
        ty (Pi q domain (weaken boxed))
      equalGlobals shared position "Pattern constructor does not transparently pack its field"
        (Apply (weaken constructor) (Variable FZ))
        (BoxValue (weaken boxed) (Variable FZ))
    (2, Lambda q domain (Lambda r second _)) => do
      let pair = Sigma q r domain second
      equalGlobals shared position "Pattern constructor type does not match the typed fields; instantiate erased parameters explicitly"
        ty (Pi q domain (Pi r second (weaken (weaken pair))))
      equalGlobals shared position "Pattern constructor does not transparently pack its fields in order"
        (Apply (Apply (weaken (weaken constructor)) (Variable (FS FZ))) (Variable FZ))
        (PairValue (weaken (weaken pair)) (Variable (FS FZ)) (Variable FZ))
    _ => Left (CannotElaborate position "Named record patterns require one or two typed field binders")

exposeGlobals : GlobalContext -> Position -> Term n -> Either ResolveError (Term n)
exposeGlobals shared position ty = case weakHeadGlobals (globalValue shared) typeReductionFuel ty of
  HeadForm result => Right result
  HeadLimit _ => Left (CannotElaborate position "Constructor field inference exhausted its reduction budget")

||| Infer the complete unary/binary field telescope, not erased parameters.
||| Canonical packing is checked before elaborating the pattern body.
public export
inferConstructorFieldsGlobals : GlobalContext -> Position -> Nat -> Context n -> Term n -> Either ResolveError (ConstructorFields n)
inferConstructorFieldsGlobals shared position arity context constructor = do
  ty <- case inferErasedGlobals shared checkingDepth typeReductionFuel context constructor of
    Left err => Left (CannotElaborate position ("Cannot infer pattern constructor fields: " ++ show err))
    Right ty => exposeGlobals shared position ty
  case (arity, ty) of
    (1, Pi q domain _) => do
      if typeNodes domain > inferredFieldNodes
         then Left (CannotElaborate position "Inferred constructor fields exceed 512 nodes; use typed pattern binders") else Right ()
      checkConstructorGlobals shared position 1 context constructor (Lambda q domain UnitValue)
      Right (OneField q domain)
    (2, Pi q domain rest) => do
      rest <- exposeGlobals shared position rest
      case rest of
        Pi r second _ => do
          if typeNodes domain + typeNodes second > inferredFieldNodes
             then Left (CannotElaborate position "Inferred constructor fields exceed 512 nodes; use typed pattern binders") else Right ()
          checkConstructorGlobals shared position 2 context constructor (Lambda q domain (Lambda r second UnitValue))
          Right (TwoFields q domain r second)
        _ => Left (CannotElaborate position "Constructor does not expose two fields; instantiate erased parameters explicitly")
    _ => Left (CannotElaborate position "Constructor does not expose the requested fields; instantiate erased parameters explicitly")

-- Closed-syntax compatibility APIs. Shared programs pass their checked context explicitly.
public export
checkConstructor : Position -> Nat -> Context n -> Term n -> Term n -> Either ResolveError ()
checkConstructor = checkConstructorGlobals emptyGlobals

public export
checkedSequenceConstructor : Position -> Context n -> Term n -> Term n -> GlobalDefinition -> Either ResolveError Nat
checkedSequenceConstructor = checkedSequenceConstructorGlobals emptyGlobals

public export
inferConstructorFields : Position -> Nat -> Context n -> Term n -> Either ResolveError (ConstructorFields n)
inferConstructorFields = inferConstructorFieldsGlobals emptyGlobals
