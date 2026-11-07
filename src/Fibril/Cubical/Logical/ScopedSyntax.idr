-- Uniform scoped candidates, not intrinsically typed terms or checked evidence.
module Fibril.Cubical.Logical.ScopedSyntax

import Data.Fin
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

||| Both types and terms inhabit this syntax. Path families bind one dimension;
||| endpoints live in the outer dimension scope. This permits PathP-shaped,
||| dimension-dependent candidates, not dependent PathP typing. No constructor
||| asserts typing, and this module adds no surface parser syntax.
public export
data Expr : Nat -> Nat -> Type where
  Variable : Fin m -> Expr m n
  Universe : Expr m n
  Path : Expr m (S n) -> Expr m n -> Expr m n -> Expr m n
  Abstract : Expr m (S n) -> Expr m n
  Apply : Expr m n -> ScopedInterval n -> Expr m n

public export
liftDimensions : (Fin n -> ScopedInterval d) -> Fin (S n) -> ScopedInterval (S d)
liftDimensions env FZ = Var FZ
liftDimensions env (FS i) = weakenInterval (env i)

public export
substituteDimensions : (Fin n -> ScopedInterval d) -> Expr m n -> Expr m d
substituteDimensions env (Variable x) = Variable x
substituteDimensions env Universe = Universe
substituteDimensions env (Path a l r) = Path (substituteDimensions (liftDimensions env) a) (substituteDimensions env l) (substituteDimensions env r)
substituteDimensions env (Abstract body) = Abstract (substituteDimensions (liftDimensions env) body)
substituteDimensions env (Apply p i) = Apply (substituteDimensions env p) (substituteScoped env i)

public export
renameTerms : (Fin m -> Fin k) -> Expr m n -> Expr k n
renameTerms env (Variable x) = Variable (env x)
renameTerms env Universe = Universe
renameTerms env (Path a l r) = Path (renameTerms env a) (renameTerms env l) (renameTerms env r)
renameTerms env (Abstract body) = Abstract (renameTerms env body)
renameTerms env (Apply p i) = Apply (renameTerms env p) i

public export
weakenDimensions : Expr m n -> Expr m (S n)
weakenDimensions = substituteDimensions (Var . FS)

||| Term substitutions are lifted by weakening each replacement under a dimension binder.
public export
substituteTerms : (Fin m -> Expr k n) -> Expr m n -> Expr k n
substituteTerms env (Variable x) = env x
substituteTerms env Universe = Universe
substituteTerms env (Path a l r) = Path (substituteTerms (weakenDimensions . env) a) (substituteTerms env l) (substituteTerms env r)
substituteTerms env (Abstract body) = Abstract (substituteTerms (weakenDimensions . env) body)
substituteTerms env (Apply p i) = Apply (substituteTerms env p) i

public export
termIdentity : (e : Expr m n) -> substituteTerms Variable e = e
termIdentity (Variable x) = Refl
termIdentity Universe = Refl
termIdentity (Path a l r) = rewrite termIdentity a in rewrite termIdentity l in rewrite termIdentity r in Refl
termIdentity (Abstract body) = rewrite termIdentity body in Refl
termIdentity (Apply p i) = rewrite termIdentity p in Refl

intervalIdentityWith : (env : Fin n -> ScopedInterval n) ->
                       ((i : Fin n) -> env i = Var i) ->
                       (r : ScopedInterval n) -> substituteScoped env r = r
intervalIdentityWith env h Zero = Refl
intervalIdentityWith env h One = Refl
intervalIdentityWith env h (Var i) = h i
intervalIdentityWith env h (Meet a b) = rewrite intervalIdentityWith env h a in rewrite intervalIdentityWith env h b in Refl
intervalIdentityWith env h (Join a b) = rewrite intervalIdentityWith env h a in rewrite intervalIdentityWith env h b in Refl
intervalIdentityWith env h (Reverse a) = rewrite intervalIdentityWith env h a in Refl

liftIdentity : (env : Fin n -> ScopedInterval n) ->
               ((i : Fin n) -> env i = Var i) ->
               (i : Fin (S n)) -> liftDimensions env i = Var i
liftIdentity env h FZ = Refl
liftIdentity env h (FS i) = rewrite h i in Refl

public export
dimensionIdentityWith : (env : Fin n -> ScopedInterval n) ->
                        ((i : Fin n) -> env i = Var i) ->
                        (e : Expr m n) -> substituteDimensions env e = e
dimensionIdentityWith env h (Variable x) = Refl
dimensionIdentityWith env h Universe = Refl
dimensionIdentityWith env h (Path a l r) =
  rewrite dimensionIdentityWith (liftDimensions env) (liftIdentity env h) a in
  rewrite dimensionIdentityWith env h l in rewrite dimensionIdentityWith env h r in Refl
dimensionIdentityWith env h (Abstract body) =
  rewrite dimensionIdentityWith (liftDimensions env) (liftIdentity env h) body in Refl
dimensionIdentityWith env h (Apply p i) =
  rewrite dimensionIdentityWith env h p in rewrite intervalIdentityWith env h i in Refl

public export
dimensionIdentity : (e : Expr m n) -> substituteDimensions Var e = e
dimensionIdentity = dimensionIdentityWith Var (\_ => Refl)
