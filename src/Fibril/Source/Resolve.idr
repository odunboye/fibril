-- Lexical name resolution into bounded de Bruijn indices, not type inference.
module Fibril.Source.Resolve

import Data.Fin
import Data.Vect
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax
import Fibril.Source.Global

%default total

||| An unresolved name at its original scalar location.
public export
record ResolveError where
  constructor Unbound
  position : Position
  name : String

public export
Show ResolveError where
  show err = show err.position ++ ": Unbound name " ++ show err.name

lookupName : String -> Vect n String -> Maybe (Fin n)
lookupName name [] = Nothing
lookupName name (bound :: rest) =
  if name == bound then Just FZ else map FS (lookupName name rest)

||| Resolve with newest-first names. Binder domains see the old environment;
||| bodies see the new binder. Shadowing resolves to the nearest binder.
||| Underscore is a wildcard and cannot be referenced.
public export
resolveInWith : List GlobalDefinition -> Vect n String -> Expr -> Either ResolveError (Term n)
resolveInWith globals env (NRef span name) =
  if name == "_" then Left (Unbound span.start name)
     else case lookupName name env of
       Nothing => case lookupGlobal name globals of
         Nothing => Left (Unbound span.start name)
         Just value => Right (rename absurd value)
       Just index => Right (Variable index)
resolveInWith globals env (NSort span level) = Right (Universe level)
resolveInWith globals env (NUnitType span) = Right UnitType
resolveInWith globals env (NUnitValue span) = Right UnitValue
resolveInWith globals env (NStringType span) = Right StringType
resolveInWith globals env (NStringValue span value) = Right (StringValue value)
resolveInWith globals env (NBoolType span) = Right BoolType
resolveInWith globals env (NBoolValue span True) = Right BoolTrue
resolveInWith globals env (NBoolValue span False) = Right BoolFalse
resolveInWith globals env (NIf span condition yes no) =
  [| BoolCase (resolveInWith globals env condition) (resolveInWith globals env yes) (resolveInWith globals env no) |]
resolveInWith globals env (NUnitCase span scrutinee body) =
  [| UnitCase (resolveInWith globals env scrutinee) (resolveInWith globals env body) |]
resolveInWith globals env (NPi span q name domain body) = do
  domain <- resolveInWith globals env domain
  body <- resolveInWith globals (name :: env) body
  Right (Pi q domain body)
resolveInWith globals env (NLambda span q name domain body) = do
  domain <- resolveInWith globals env domain
  body <- resolveInWith globals (name :: env) body
  Right (Lambda q domain body)
resolveInWith globals env (NApply span function argument) =
  [| Apply (resolveInWith globals env function) (resolveInWith globals env argument) |]
resolveInWith globals env (NSequence span first rest) = do
  action <- resolveInWith globals env first
  following <- resolveInWith globals env rest
  Right (IOBind UnitType UnitType action
    (Lambda Linear UnitType (UnitCase (Variable FZ) (weaken following))))
resolveInWith globals env (NDoBind span name domain action body) = do
  ty <- resolveInWith globals env domain
  action <- resolveInWith globals env action
  body <- resolveInWith globals (name :: env) body
  Right (IOBind ty UnitType action (Lambda Linear ty body))
-- Checking an identity application enforces the expected domain using existing
-- typing/compatibility rules. Linear use preserves the term's runtime usage.
resolveInWith globals env (NAscribe span term expected) = do
  term <- resolveInWith globals env term
  ty <- resolveInWith globals env expected
  Right (Apply (Lambda Linear ty (Variable FZ)) term)

-- The binding is nonrecursive: annotation and value use the outer environment.
-- A lambda/application enforces the annotation and declared resource quantity.
resolveInWith globals env (NLet span q name expected value body) = do
  ty <- resolveInWith globals env expected
  value <- resolveInWith globals env value
  body <- resolveInWith globals (name :: env) body
  Right (Apply (Lambda q ty body) value)

||| Lexical-only compatibility API.
public export
resolveIn : Vect n String -> Expr -> Either ResolveError (Term n)
resolveIn = resolveInWith []

public export
resolveClosed : Expr -> Either ResolveError (Term 0)
resolveClosed = resolveIn []

||| Explicit closed-definition environment; lexical bindings take precedence.
public export
resolveClosedWith : List GlobalDefinition -> Expr -> Either ResolveError (Term 0)
resolveClosedWith globals = resolveInWith globals []
