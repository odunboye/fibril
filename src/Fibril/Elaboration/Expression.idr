-- Contextual named-to-core elaboration; ordinary core checking remains independent.
module Fibril.Elaboration.Expression

import Data.Fin
import Data.Vect
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Global
import public Fibril.Source.Resolve.Error
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Reduction
import Fibril.Core.Limits
import Fibril.Elaboration.Expression.Scope
import Fibril.Elaboration.Expression.Motive
import Fibril.Elaboration.Expression.Constructor
import Fibril.Elaboration.Expression.Parameters
import Fibril.Elaboration.Expression.Dictionary

%default total

lookupName : String -> Vect n String -> Maybe (Fin n)
lookupName name [] = Nothing
lookupName name (bound :: rest) =
  if name == bound then Just FZ else map FS (lookupName name rest)

boundedResult : Position -> Term n -> Either ResolveError (Term n)
boundedResult position result = do
  if typeNodes result > inferredResultNodes then Left (CannotElaborate position "Inferred motive result type exceeds 512 nodes; use an explicit return motive") else Right ()
  normal <- case normalize typeReductionFuel result of
    Normal value => Right value
    OutOfFuel _ => Left (CannotElaborate position "Motive inference reduction budget exhausted; use an explicit return motive")
  if typeNodes normal > inferredResultNodes then Left (CannotElaborate position "Inferred motive result type exceeds 512 nodes; use an explicit return motive") else Right normal

inferCase : Position -> Nat -> Context n -> Term n -> Term n -> Either ResolveError (Term n)
inferCase position arity context scrutinee branch = do
  branchType <- case inferErased checkingDepth typeReductionFuel context branch of
    Left err => Left (CannotElaborate position ("Cannot infer record branch type: " ++ show err))
    Right ty => Right ty
  case (arity, branch, branchType) of
    (1, Lambda q domain _, Pi _ _ result) => do
      result <- boundedResult position result
      motive <- unaryMotive position q domain result
      Right (BoxCase motive scrutinee branch)
    (2, Lambda q domain (Lambda r second _), Pi _ _ (Pi _ _ result)) => do
      result <- boundedResult position result
      motive <- binaryMotive position q r domain second result
      Right (PairCase motive scrutinee branch)
    _ => Left (CannotElaborate position "Record motive inference requires one or two typed pattern binders")

namedConstructor : Expr -> Bool
namedConstructor (NRef _ _) = True
namedConstructor (NQualifiedRef _ _) = True
namedConstructor (NApply _ function _) = namedConstructor function
namedConstructor _ = False

mutual
  ||| Resolve with newest-first names. Binder domains see the old environment;
  ||| bodies see the new binder. Shadowing resolves to the nearest binder.
  ||| Underscore is a wildcard and cannot be referenced.
  public export
  elaborateInWith : List GlobalDefinition -> Maybe (Context n) -> Vect n String -> Expr -> Either ResolveError (Term n)
  elaborateInWith globals context env (NRef span name) =
    if name == "_" then Left (Unbound span.start name)
       else case lookupName name env of
         Nothing => case lookupGlobal name globals of
           Nothing => Left (Unbound span.start name)
           Just value => Right (rename absurd value)
         Just index => Right (Variable index)
  elaborateInWith globals context env (NQualifiedRef span name) =
    case lookupGlobal name globals of
      Nothing => Left (Unbound span.start name)
      Just value => Right (rename absurd value)
  elaborateInWith globals context env (NSort span level) = Right (Universe level)
  elaborateInWith globals context env (NUnitType span) = Right UnitType
  elaborateInWith globals context env (NUnitValue span) = Right UnitValue
  elaborateInWith globals context env (NStringType span) = Right StringType
  elaborateInWith globals context env (NStringValue span value) = Right (StringValue value)
  elaborateInWith globals context env (NBoolType span) = Right BoolType
  elaborateInWith globals context env (NBoolValue span True) = Right BoolTrue
  elaborateInWith globals context env (NBoolValue span False) = Right BoolFalse
  elaborateInWith globals context env (NIf span condition yes no) =
    [| BoolCase (elaborateInWith globals context env condition) (elaborateInWith globals context env yes) (elaborateInWith globals context env no) |]
  elaborateInWith globals context env (NUnitCase span scrutinee body) =
    [| UnitCase (elaborateInWith globals context env scrutinee) (elaborateInWith globals context env body) |]
  elaborateInWith globals context env (NSigma span q r name domain body) = do
    domain <- elaborateInWith globals context env domain
    body <- elaborateInWith globals (map (\ctx => Extend ctx q domain) context) (name :: env) body
    Right (Sigma q r domain body)
  elaborateInWith globals context env (NPairValue span ty first second) =
    [| PairValue (elaborateInWith globals context env ty) (elaborateInWith globals context env first) (elaborateInWith globals context env second) |]
  elaborateInWith globals context env (NBoxType span q ty) = [| BoxType (pure q) (elaborateInWith globals context env ty) |]
  elaborateInWith globals context env (NBoxValue span ty value) = [| BoxValue (elaborateInWith globals context env ty) (elaborateInWith globals context env value) |]
  elaborateInWith globals context env (NBoxCase span motive value branch) =
    [| BoxCase (elaborateInWith globals context env motive) (elaborateInWith globals context env value) (elaborateInWith globals context env branch) |]
  elaborateInWith globals context env (NPatternLambda span _ _) =
    Left (CannotElaborate span.start "Inferred field binders require a constructor-named pattern")
  elaborateInWith globals context env (NConstructorCase span arity constructor scrutinee branch motive) = do
    if not (namedConstructor constructor)
       then Left (CannotElaborate (extent constructor).start "Pattern constructor must be a named function, optionally explicitly instantiated") else Right ()
    typedContext <- case context of
      Nothing => Left (CannotElaborate span.start "Named pattern checking requires a typed context")
      Just ctx => Right ctx
    candidate <- elaborateInWith globals context env constructor
    value <- elaborateInWith globals context env scrutinee
    named <- instantiateParameters (extent constructor).start arity typedContext candidate value
    branch <- elaboratePatternBranch globals typedContext env (extent constructor).start arity named branch
    case motive of
      Nothing => inferCase span.start arity typedContext value branch
      Just authored => do
        explicit <- elaborateInWith globals context env authored
        Right (if arity == 1 then BoxCase explicit value branch else PairCase explicit value branch)
  elaborateInWith globals context env (NInferCase span arity scrutinee branch) = do
    typedContext <- case context of
      Nothing => Left (CannotElaborate span.start "Motive inference requires a typed context; use contextual expression elaboration")
      Just ctx => Right ctx
    value <- elaborateInWith globals context env scrutinee
    branch <- elaborateInWith globals context env branch
    inferCase span.start arity typedContext value branch
  elaborateInWith globals context env (NPairCase span motive value branch) =
    [| PairCase (elaborateInWith globals context env motive) (elaborateInWith globals context env value) (elaborateInWith globals context env branch) |]
  elaborateInWith globals context env (NConstraintPi span q name domain body) = do
    domain <- elaborateInWith globals context env domain
    constraintType span.start q domain
    body <- elaborateInWith globals (map (\ctx => Extend ctx q domain) context) (name :: env) body
    Right (Pi q domain body)
  elaborateInWith globals context env (NImplementationApply span origin function) = do
    typed <- case context of
      Nothing => Left (CannotElaborate origin.start "Implementation lookup requires a typed context")
      Just ctx => Right ctx
    function <- elaborateInWith globals context env function
    selectImplementation origin.start globals typed function
  elaborateInWith globals context env (NDictionaryApply span origin function argument) = do
    typed <- case context of
      Nothing => Left (CannotElaborate origin.start "Dictionary selection requires a typed context")
      Just ctx => Right ctx
    function <- elaborateInWith globals context env function
    argument <- case argument of
      Nothing => Right Nothing
      Just value => Just <$> elaborateInWith globals context env value
    selectDictionary origin.start typed env function argument
  elaborateInWith globals context env (NPi span q name domain body) = do
    domain <- elaborateInWith globals context env domain
    body <- elaborateInWith globals (map (\ctx => Extend ctx q domain) context) (name :: env) body
    Right (Pi q domain body)
  elaborateInWith globals context env (NLambda span q name domain body) = do
    domain <- elaborateInWith globals context env domain
    body <- elaborateInWith globals (map (\ctx => Extend ctx q domain) context) (name :: env) body
    Right (Lambda q domain body)
  elaborateInWith globals context env (NInfix span function left right) = do
    operator <- elaborateInWith globals context env function
    left <- elaborateInWith globals context env left
    right <- elaborateInWith globals context env right
    Right (Apply (Apply operator left) right)
  elaborateInWith globals context env (NApply span function argument) =
    [| Apply (elaborateInWith globals context env function) (elaborateInWith globals context env argument) |]
  elaborateInWith globals context env (NSequence span first rest) = do
    action <- elaborateInWith globals context env first
    following <- elaborateInWith globals context env rest
    Right (IOBind UnitType UnitType action
      (Lambda Linear UnitType (UnitCase (Variable FZ) (weaken following))))
  elaborateInWith globals context env (NDoBind span name domain action body) = do
    ty <- elaborateInWith globals context env domain
    action <- elaborateInWith globals context env action
    body <- elaborateInWith globals (map (\ctx => Extend ctx Linear ty) context) (name :: env) body
    Right (IOBind ty UnitType action (Lambda Linear ty body))
  -- Checking an identity application enforces the expected domain using existing
  -- typing/compatibility rules. Linear use preserves the term's runtime usage.
  elaborateInWith globals context env (NAscribe span term expected) = do
    term <- elaborateInWith globals context env term
    ty <- elaborateInWith globals context env expected
    Right (Apply (Lambda Linear ty (Variable FZ)) term)

  -- The binding is nonrecursive: annotation and value use the outer environment.
  -- A lambda/application enforces the annotation and declared resource quantity.
  elaborateInWith globals context env (NLet span q name expected value body) = do
    ty <- elaborateInWith globals context env expected
    value <- elaborateInWith globals context env value
    body <- elaborateInWith globals (map (\ctx => Extend ctx q ty) context) (name :: env) body
    Right (Apply (Lambda q ty body) value)

  elaborateInWith globals context env (NDoResult span result body) = do
    ty <- elaborateInWith globals context env result
    value <- elaborateDo globals context env ty body
    Right (Apply (Lambda Linear (IOType ty) (Variable FZ)) value)

  elaboratePatternBranch : List GlobalDefinition -> Context n -> Vect n String -> Position ->
                           Nat -> Term n -> Expr -> Either ResolveError (Term n)
  elaboratePatternBranch globals context env position arity constructor (NPatternLambda span names body) = do
    fields <- inferConstructorFields position arity context constructor
    case (fields, names) of
      (OneField q domain, [name]) => do
        body <- elaborateInWith globals (Just (Extend context q domain)) (name.spelling :: env) body
        Right (Lambda q domain body)
      (TwoFields q domain r second, [first, last]) => do
        body <- elaborateInWith globals (Just (Extend (Extend context q domain) r second))
                  (last.spelling :: first.spelling :: env) body
        Right (Lambda q domain (Lambda r second body))
      _ => Left (CannotElaborate span.start "Constructor field count does not match the pattern names")
  elaboratePatternBranch globals context env position arity constructor branch = do
    resolved <- elaborateInWith globals (Just context) env branch
    checkConstructor position arity context constructor resolved
    Right resolved

  -- The block result is resolved outside its statements and weakened under each
  -- local binder. It must never be re-resolved under a shadowing statement name.
  elaborateDo : List GlobalDefinition -> Maybe (Context n) -> Vect n String -> Term n -> Expr ->
              Either ResolveError (Term n)
  elaborateDo globals context env result (NSequence span first rest) = do
    action <- elaborateInWith globals context env first
    following <- elaborateDo globals context env result rest
    Right (IOBind UnitType result action
      (Lambda Linear UnitType (UnitCase (Variable FZ) (weaken following))))
  elaborateDo globals context env result (NDoBind span name domain action body) = do
    ty <- elaborateInWith globals context env domain
    action <- elaborateInWith globals context env action
    body <- elaborateDo globals (map (\ctx => Extend ctx Linear ty) context) (name :: env) (weaken result) body
    Right (IOBind ty result action (Lambda Linear ty body))
  elaborateDo globals context env result (NLet span q name expected value body) = do
    ty <- elaborateInWith globals context env expected
    value <- elaborateInWith globals context env value
    body <- elaborateDo globals (map (\ctx => Extend ctx q ty) context) (name :: env) (weaken result) body
    Right (Apply (Lambda q ty body) value)
  elaborateDo globals context env result term = elaborateInWith globals context env term

||| Contextual elaboration of a closed source expression.
public export
elaborateClosedWith : List GlobalDefinition -> Expr -> Either ResolveError (Term 0)
elaborateClosedWith globals = elaborateInWith globals (Just Empty) []

public export
elaborateClosed : Expr -> Either ResolveError (Term 0)
elaborateClosed = elaborateClosedWith []
