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
import Fibril.Source.Text
import Fibril.Source.Resolve.Error

%default total

public export
inferredFieldNodes : Nat
inferredFieldNodes = 512

public export
data ConstructorFields : Nat -> Type where
  OneField : Quantity -> Term n -> ConstructorFields n
  TwoFields : Quantity -> Term n -> Quantity -> Term (S n) -> ConstructorFields n

equal : Position -> String -> Term n -> Term n -> Either ResolveError ()
equal position message actual expected = case betaCompare typeReductionFuel actual expected of
  EqualNormalForms => Right ()
  DifferentNormalForms => Left (CannotElaborate position message)
  Inconclusive => Left (CannotElaborate position "Pattern constructor comparison exhausted its reduction budget")

||| The constructor expression is compile-time data, not part of the emitted case.
||| No nominal identity or runtime constructor discrimination is asserted.
public export
checkConstructor : Position -> Nat -> Context n -> Term n -> Term n -> Either ResolveError ()
checkConstructor position arity context constructor branch = do
  ty <- case inferErased checkingDepth typeReductionFuel context constructor of
    Left err => Left (CannotElaborate position ("Cannot infer pattern constructor type: " ++ show err))
    Right ty => Right ty
  case (arity, branch) of
    (1, Lambda q domain _) => do
      let boxed = BoxType q domain
      equal position "Pattern constructor type does not match the typed fields; instantiate erased parameters explicitly"
        ty (Pi q domain (weaken boxed))
      equal position "Pattern constructor does not transparently pack its field"
        (Apply (weaken constructor) (Variable FZ))
        (BoxValue (weaken boxed) (Variable FZ))
    (2, Lambda q domain (Lambda r second _)) => do
      let pair = Sigma q r domain second
      equal position "Pattern constructor type does not match the typed fields; instantiate erased parameters explicitly"
        ty (Pi q domain (Pi r second (weaken (weaken pair))))
      equal position "Pattern constructor does not transparently pack its fields in order"
        (Apply (Apply (weaken (weaken constructor)) (Variable (FS FZ))) (Variable FZ))
        (PairValue (weaken (weaken pair)) (Variable (FS FZ)) (Variable FZ))
    _ => Left (CannotElaborate position "Named record patterns require one or two typed field binders")

expose : Position -> Term n -> Either ResolveError (Term n)
expose position ty = case weakHead typeReductionFuel ty of
  HeadForm result => Right result
  HeadLimit _ => Left (CannotElaborate position "Constructor field inference exhausted its reduction budget")

||| Infer the complete unary/binary field telescope, not erased parameters.
||| Canonical packing is checked before elaborating the pattern body.
public export
inferConstructorFields : Position -> Nat -> Context n -> Term n -> Either ResolveError (ConstructorFields n)
inferConstructorFields position arity context constructor = do
  ty <- case inferErased checkingDepth typeReductionFuel context constructor of
    Left err => Left (CannotElaborate position ("Cannot infer pattern constructor fields: " ++ show err))
    Right ty => expose position ty
  case (arity, ty) of
    (1, Pi q domain _) => do
      if typeNodes domain > inferredFieldNodes
         then Left (CannotElaborate position "Inferred constructor fields exceed 512 nodes; use typed pattern binders") else Right ()
      checkConstructor position 1 context constructor (Lambda q domain UnitValue)
      Right (OneField q domain)
    (2, Pi q domain rest) => do
      rest <- expose position rest
      case rest of
        Pi r second _ => do
          if typeNodes domain + typeNodes second > inferredFieldNodes
             then Left (CannotElaborate position "Inferred constructor fields exceed 512 nodes; use typed pattern binders") else Right ()
          checkConstructor position 2 context constructor (Lambda q domain (Lambda r second UnitValue))
          Right (TwoFields q domain r second)
        _ => Left (CannotElaborate position "Constructor does not expose two fields; instantiate erased parameters explicitly")
    _ => Left (CannotElaborate position "Constructor does not expose the requested fields; instantiate erased parameters explicitly")
