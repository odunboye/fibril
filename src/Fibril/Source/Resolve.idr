-- Lexical name resolution into bounded de Bruijn indices, not type inference.
module Fibril.Source.Resolve

import Data.Fin
import Data.Vect
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Syntax

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
resolveIn : Vect n String -> Expr -> Either ResolveError (Term n)
resolveIn env (NRef span name) =
  if name == "_" then Left (Unbound span.start name)
     else case lookupName name env of
       Nothing => Left (Unbound span.start name)
       Just index => Right (Variable index)
resolveIn env (NSort span level) = Right (Universe level)
resolveIn env (NUnitType span) = Right UnitType
resolveIn env (NUnitValue span) = Right UnitValue
resolveIn env (NBoolType span) = Right BoolType
resolveIn env (NBoolValue span True) = Right BoolTrue
resolveIn env (NBoolValue span False) = Right BoolFalse
resolveIn env (NIf span condition yes no) =
  [| BoolCase (resolveIn env condition) (resolveIn env yes) (resolveIn env no) |]
resolveIn env (NUnitCase span scrutinee body) =
  [| UnitCase (resolveIn env scrutinee) (resolveIn env body) |]
resolveIn env (NPi span q name domain body) = do
  domain <- resolveIn env domain
  body <- resolveIn (name :: env) body
  Right (Pi q domain body)
resolveIn env (NLambda span q name domain body) = do
  domain <- resolveIn env domain
  body <- resolveIn (name :: env) body
  Right (Lambda q domain body)
resolveIn env (NApply span function argument) =
  [| Apply (resolveIn env function) (resolveIn env argument) |]
-- Checking an identity application enforces the expected domain using existing
-- typing/compatibility rules. Linear use preserves the term's runtime usage.
resolveIn env (NAscribe span term expected) = do
  term <- resolveIn env term
  ty <- resolveIn env expected
  Right (Apply (Lambda Linear ty (Variable FZ)) term)

-- The binding is nonrecursive: annotation and value use the outer environment.
-- A lambda/application enforces the annotation and declared resource quantity.
resolveIn env (NLet span q name expected value body) = do
  ty <- resolveIn env expected
  value <- resolveIn env value
  body <- resolveIn (name :: env) body
  Right (Apply (Lambda q ty body) value)

||| Resolve a closed expression, including lowered declaration lets.
||| There is no separate global namespace or import environment.
public export
resolveClosed : Expr -> Either ResolveError (Term 0)
resolveClosed = resolveIn []
