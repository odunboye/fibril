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

||| Pointwise equal interval environments act equally on interval syntax.
public export
intervalSubstitutionCongruence : (env, env' : Fin n -> ScopedInterval d) ->
  ((i : Fin n) -> env i = env' i) -> (r : ScopedInterval n) ->
  substituteScoped env r = substituteScoped env' r
intervalSubstitutionCongruence env env' h Zero = Refl
intervalSubstitutionCongruence env env' h One = Refl
intervalSubstitutionCongruence env env' h (Var i) = h i
intervalSubstitutionCongruence env env' h (Meet a b) =
  rewrite intervalSubstitutionCongruence env env' h a in
  rewrite intervalSubstitutionCongruence env env' h b in Refl
intervalSubstitutionCongruence env env' h (Join a b) =
  rewrite intervalSubstitutionCongruence env env' h a in
  rewrite intervalSubstitutionCongruence env env' h b in Refl
intervalSubstitutionCongruence env env' h (Reverse a) =
  rewrite intervalSubstitutionCongruence env env' h a in Refl

||| Lifting preserves pointwise equality, including the fresh bound dimension.
public export
liftDimensionsCongruence : (env, env' : Fin n -> ScopedInterval d) ->
  ((i : Fin n) -> env i = env' i) -> (i : Fin (S n)) ->
  liftDimensions env i = liftDimensions env' i
liftDimensionsCongruence env env' h FZ = Refl
liftDimensionsCongruence env env' h (FS i) = rewrite h i in Refl

public export
dimensionSubstitutionCongruence : (env, env' : Fin n -> ScopedInterval d) ->
  ((i : Fin n) -> env i = env' i) -> (e : Expr m n) ->
  substituteDimensions env e = substituteDimensions env' e
dimensionSubstitutionCongruence env env' h (Variable x) = Refl
dimensionSubstitutionCongruence env env' h Universe = Refl
dimensionSubstitutionCongruence env env' h (Path a l r) =
  rewrite dimensionSubstitutionCongruence (liftDimensions env) (liftDimensions env') (liftDimensionsCongruence env env' h) a in
  rewrite dimensionSubstitutionCongruence env env' h l in
  rewrite dimensionSubstitutionCongruence env env' h r in Refl
dimensionSubstitutionCongruence env env' h (Abstract body) =
  rewrite dimensionSubstitutionCongruence (liftDimensions env) (liftDimensions env') (liftDimensionsCongruence env env' h) body in Refl
dimensionSubstitutionCongruence env env' h (Apply p i) =
  rewrite dimensionSubstitutionCongruence env env' h p in
  rewrite intervalSubstitutionCongruence env env' h i in Refl

public export
termSubstitutionCongruence : (env, env' : Fin m -> Expr k n) ->
  ((i : Fin m) -> env i = env' i) -> (e : Expr m n) ->
  substituteTerms env e = substituteTerms env' e
termSubstitutionCongruence env env' h (Variable x) = h x
termSubstitutionCongruence env env' h Universe = Refl
termSubstitutionCongruence env env' h (Path a l r) =
  rewrite termSubstitutionCongruence (weakenDimensions . env) (weakenDimensions . env') (\i => cong weakenDimensions (h i)) a in
  rewrite termSubstitutionCongruence env env' h l in
  rewrite termSubstitutionCongruence env env' h r in Refl
termSubstitutionCongruence env env' h (Abstract body) =
  rewrite termSubstitutionCongruence (weakenDimensions . env) (weakenDimensions . env') (\i => cong weakenDimensions (h i)) body in Refl
termSubstitutionCongruence env env' h (Apply p i) =
  rewrite termSubstitutionCongruence env env' h p in Refl

||| Term renaming composes without changing dimension binders or intervals.
public export
renameTermsComposition : (first : Fin m -> Fin k) -> (second : Fin k -> Fin j) ->
  (e : Expr m n) -> renameTerms second (renameTerms first e) = renameTerms (second . first) e
renameTermsComposition first second (Variable x) = Refl
renameTermsComposition first second Universe = Refl
renameTermsComposition first second (Path a l r) =
  rewrite renameTermsComposition first second a in
  rewrite renameTermsComposition first second l in
  rewrite renameTermsComposition first second r in Refl
renameTermsComposition first second (Abstract body) =
  rewrite renameTermsComposition first second body in Refl
renameTermsComposition first second (Apply p i) =
  rewrite renameTermsComposition first second p in Refl

public export
intervalSubstitutionComposition : (first : Fin n -> ScopedInterval d) ->
  (second : Fin d -> ScopedInterval q) -> (r : ScopedInterval n) ->
  substituteScoped second (substituteScoped first r) =
  substituteScoped (substituteScoped second . first) r
intervalSubstitutionComposition first second Zero = Refl
intervalSubstitutionComposition first second One = Refl
intervalSubstitutionComposition first second (Var i) = Refl
intervalSubstitutionComposition first second (Meet a b) =
  rewrite intervalSubstitutionComposition first second a in
  rewrite intervalSubstitutionComposition first second b in Refl
intervalSubstitutionComposition first second (Join a b) =
  rewrite intervalSubstitutionComposition first second a in
  rewrite intervalSubstitutionComposition first second b in Refl
intervalSubstitutionComposition first second (Reverse a) =
  rewrite intervalSubstitutionComposition first second a in Refl

||| Substitution under a fresh binder commutes with weakening an interval.
public export
liftDimensionsWeakening : (env : Fin n -> ScopedInterval d) ->
  (r : ScopedInterval n) ->
  substituteScoped (liftDimensions env) (weakenInterval r) =
  weakenInterval (substituteScoped env r)
liftDimensionsWeakening env r =
  trans (intervalSubstitutionComposition (Var . FS) (liftDimensions env) r)
    (sym (intervalSubstitutionComposition env (Var . FS) r))

public export
liftDimensionsComposition : (first : Fin n -> ScopedInterval d) ->
  (second : Fin d -> ScopedInterval q) -> (i : Fin (S n)) ->
  substituteScoped (liftDimensions second) (liftDimensions first i) =
  liftDimensions (substituteScoped second . first) i
liftDimensionsComposition first second FZ = Refl
liftDimensionsComposition first second (FS i) = liftDimensionsWeakening second (first i)

||| Simultaneous dimension substitutions compose, including under both binders.
public export
dimensionSubstitutionComposition : (first : Fin n -> ScopedInterval d) ->
  (second : Fin d -> ScopedInterval q) -> (e : Expr m n) ->
  substituteDimensions second (substituteDimensions first e) =
  substituteDimensions (substituteScoped second . first) e
dimensionSubstitutionComposition first second (Variable x) = Refl
dimensionSubstitutionComposition first second Universe = Refl
dimensionSubstitutionComposition first second (Path a l r) =
  rewrite dimensionSubstitutionComposition (liftDimensions first) (liftDimensions second) a in
  rewrite dimensionSubstitutionCongruence _ _ (liftDimensionsComposition first second) a in
  rewrite dimensionSubstitutionComposition first second l in
  rewrite dimensionSubstitutionComposition first second r in Refl
dimensionSubstitutionComposition first second (Abstract body) =
  rewrite dimensionSubstitutionComposition (liftDimensions first) (liftDimensions second) body in
  rewrite dimensionSubstitutionCongruence _ _ (liftDimensionsComposition first second) body in Refl
dimensionSubstitutionComposition first second (Apply p i) =
  rewrite dimensionSubstitutionComposition first second p in
  rewrite intervalSubstitutionComposition first second i in Refl

||| Substituting beneath a dimension binder commutes with weakening an expression.
public export
liftDimensionsExprWeakening : (env : Fin n -> ScopedInterval d) ->
  (e : Expr m n) ->
  substituteDimensions (liftDimensions env) (weakenDimensions e) =
  weakenDimensions (substituteDimensions env e)
liftDimensionsExprWeakening env e =
  trans (dimensionSubstitutionComposition (Var . FS) (liftDimensions env) e)
    (sym (dimensionSubstitutionComposition env (Var . FS) e))

||| Term and dimension substitutions commute when replacements are also
||| dimension-substituted; both actions are simultaneous, not recursive in env.
public export
termDimensionSubstitution : (terms : Fin m -> Expr k n) ->
  (dims : Fin n -> ScopedInterval d) -> (e : Expr m n) ->
  substituteDimensions dims (substituteTerms terms e) =
  substituteTerms (substituteDimensions dims . terms) (substituteDimensions dims e)
termDimensionSubstitution terms dims (Variable x) = Refl
termDimensionSubstitution terms dims Universe = Refl
termDimensionSubstitution terms dims (Path a l r) =
  rewrite termDimensionSubstitution (weakenDimensions . terms) (liftDimensions dims) a in
  rewrite termSubstitutionCongruence _ _ (\i => liftDimensionsExprWeakening dims (terms i)) (substituteDimensions (liftDimensions dims) a) in
  rewrite termDimensionSubstitution terms dims l in
  rewrite termDimensionSubstitution terms dims r in Refl
termDimensionSubstitution terms dims (Abstract body) =
  rewrite termDimensionSubstitution (weakenDimensions . terms) (liftDimensions dims) body in
  rewrite termSubstitutionCongruence _ _ (\i => liftDimensionsExprWeakening dims (terms i)) (substituteDimensions (liftDimensions dims) body) in Refl
termDimensionSubstitution terms dims (Apply p i) =
  rewrite termDimensionSubstitution terms dims p in Refl

public export
termSubstitutionWeakening : (env : Fin m -> Expr k n) -> (e : Expr m n) ->
  substituteTerms (ScopedSyntax.weakenDimensions . env) (ScopedSyntax.weakenDimensions e) =
  ScopedSyntax.weakenDimensions (substituteTerms env e)
termSubstitutionWeakening env e = sym (termDimensionSubstitution env (Var . FS) e)

||| Simultaneous term substitutions compose, weakening replacements at binders.
public export
termSubstitutionComposition : (first : Fin m -> Expr k n) ->
  (second : Fin k -> Expr j n) -> (e : Expr m n) ->
  substituteTerms second (substituteTerms first e) =
  substituteTerms (substituteTerms second . first) e
termSubstitutionComposition first second (Variable x) = Refl
termSubstitutionComposition first second Universe = Refl
termSubstitutionComposition first second (Path a l r) =
  rewrite termSubstitutionComposition (weakenDimensions . first) (weakenDimensions . second) a in
  rewrite termSubstitutionCongruence _ _ (\i => termSubstitutionWeakening second (first i)) a in
  rewrite termSubstitutionComposition first second l in
  rewrite termSubstitutionComposition first second r in Refl
termSubstitutionComposition first second (Abstract body) =
  rewrite termSubstitutionComposition (weakenDimensions . first) (weakenDimensions . second) body in
  rewrite termSubstitutionCongruence _ _ (\i => termSubstitutionWeakening second (first i)) body in Refl
termSubstitutionComposition first second (Apply p i) =
  rewrite termSubstitutionComposition first second p in Refl

||| Renaming is simultaneous substitution by variables.
public export
renameTermsAsSubstitution : (env : Fin m -> Fin k) -> (e : Expr m n) ->
  renameTerms env e = substituteTerms (Variable . env) e
renameTermsAsSubstitution env (Variable x) = Refl
renameTermsAsSubstitution env Universe = Refl
renameTermsAsSubstitution env (Path a l r) =
  rewrite renameTermsAsSubstitution env a in
  rewrite renameTermsAsSubstitution env l in
  rewrite renameTermsAsSubstitution env r in Refl
renameTermsAsSubstitution env (Abstract body) =
  rewrite renameTermsAsSubstitution env body in Refl
renameTermsAsSubstitution env (Apply p i) =
  rewrite renameTermsAsSubstitution env p in Refl

public export
renameTermsDimensionSubstitution : (terms : Fin m -> Fin k) ->
  (dims : Fin n -> ScopedInterval d) -> (e : Expr m n) ->
  renameTerms terms (substituteDimensions dims e) =
  substituteDimensions dims (renameTerms terms e)
renameTermsDimensionSubstitution terms dims (Variable x) = Refl
renameTermsDimensionSubstitution terms dims Universe = Refl
renameTermsDimensionSubstitution terms dims (Path a l r) =
  rewrite renameTermsDimensionSubstitution terms (liftDimensions dims) a in
  rewrite renameTermsDimensionSubstitution terms dims l in
  rewrite renameTermsDimensionSubstitution terms dims r in Refl
renameTermsDimensionSubstitution terms dims (Abstract body) =
  rewrite renameTermsDimensionSubstitution terms (liftDimensions dims) body in Refl
renameTermsDimensionSubstitution terms dims (Apply p i) =
  rewrite renameTermsDimensionSubstitution terms dims p in Refl
