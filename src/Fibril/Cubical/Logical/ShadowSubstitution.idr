module Fibril.Cubical.Logical.ShadowSubstitution

import Data.Vect
import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Quantitative.Substitution
import Fibril.Cubical.Logical.Shadow

%default total

public export
RenamingImage : {0 source : Vect n Ty} -> {0 target : Vect m Ty} ->
  Renaming source target -> LogicalRenaming (shadowContext source) (shadowContext target) -> Type
RenamingImage rho lr = {0 a : Ty} -> (v : Var source a) -> shadowVar (rho v) = lr (shadowVar v)

public export
liftRenamingImage : {0 binder : Ty} -> {0 source : Vect n Ty} -> {0 target : Vect m Ty} ->
  (rho : Renaming source target) -> (lr : LogicalRenaming (shadowContext source) (shadowContext target)) ->
  RenamingImage rho lr -> RenamingImage (liftRenaming {a = binder} rho) (liftLogicalRenaming lr)
liftRenamingImage rho lr agree Here = Refl
liftRenamingImage rho lr agree (There v) = cong LThere (agree v)

public export
shadowRename : {0 source : Vect n Ty} -> {0 target : Vect m Ty} ->
  (rho : Renaming source target) -> (lr : LogicalRenaming (shadowContext source) (shadowContext target)) ->
  RenamingImage rho lr -> (t : Term source a) ->
  shadowTerm (rename rho t) = renameLogical lr (shadowTerm t)
shadowRename rho lr agree (Ref v) = cong LRef (agree v)
shadowRename rho lr agree Unit = Refl
shadowRename rho lr agree (Boolean b) = Refl
shadowRename rho lr agree (Lam q body) = cong LLam (shadowRename (liftRenaming rho) (liftLogicalRenaming lr) (liftRenamingImage rho lr agree) body)
shadowRename rho lr agree (App f x) = cong2 LApp (shadowRename rho lr agree f) (shadowRename rho lr agree x)
shadowRename rho lr agree (UnitElim x b) = cong2 LUnitElim (shadowRename rho lr agree x) (shadowRename rho lr agree b)
shadowRename rho lr agree (If c t f) = rewrite shadowRename rho lr agree c in rewrite shadowRename rho lr agree t in rewrite shadowRename rho lr agree f in Refl

public export
shadowWeaken : {0 context : Vect n Ty} -> (t : Term context a) ->
  shadowTerm (weaken {b} t) = renameLogical LThere (shadowTerm t)
shadowWeaken t = shadowRename There LThere (\v => Refl) t

public export
SubstitutionImage : {0 source : Vect n Ty} -> {0 target : Vect m Ty} ->
  Substitution source target -> LogicalSubstitution (shadowContext source) (shadowContext target) -> Type
SubstitutionImage sigma ls = {0 a : Ty} -> (v : Var source a) -> shadowTerm (sigma v) = ls (shadowVar v)

public export
liftSubstitutionImage : {0 binder : Ty} -> {0 source : Vect n Ty} -> {0 target : Vect m Ty} ->
  (sigma : Substitution source target) -> (ls : LogicalSubstitution (shadowContext source) (shadowContext target)) ->
  SubstitutionImage sigma ls -> SubstitutionImage (liftSubstitution {a = binder} sigma) (liftLogicalSubstitution ls)
liftSubstitutionImage sigma ls agree Here = Refl
liftSubstitutionImage sigma ls agree (There v) = trans (shadowWeaken (sigma v)) (cong (renameLogical LThere) (agree v))

public export
shadowSubstitute : {0 source : Vect n Ty} -> {0 target : Vect m Ty} ->
  (sigma : Substitution source target) -> (ls : LogicalSubstitution (shadowContext source) (shadowContext target)) ->
  SubstitutionImage sigma ls -> (t : Term source a) ->
  shadowTerm (substitute sigma t) = substituteLogical ls (shadowTerm t)
shadowSubstitute sigma ls agree (Ref v) = agree v
shadowSubstitute sigma ls agree Unit = Refl
shadowSubstitute sigma ls agree (Boolean b) = Refl
shadowSubstitute sigma ls agree (Lam q body) = cong LLam (shadowSubstitute (liftSubstitution sigma) (liftLogicalSubstitution ls) (liftSubstitutionImage sigma ls agree) body)
shadowSubstitute sigma ls agree (App f x) = cong2 LApp (shadowSubstitute sigma ls agree f) (shadowSubstitute sigma ls agree x)
shadowSubstitute sigma ls agree (UnitElim x b) = cong2 LUnitElim (shadowSubstitute sigma ls agree x) (shadowSubstitute sigma ls agree b)
shadowSubstitute sigma ls agree (If c t f) = rewrite shadowSubstitute sigma ls agree c in rewrite shadowSubstitute sigma ls agree t in rewrite shadowSubstitute sigma ls agree f in Refl

public export
imageSubstitution : (source : Vect n Ty) -> {0 target : Vect m Ty} ->
  Substitution source target -> LogicalSubstitution (shadowContext source) (shadowContext target)
imageSubstitution [] sigma v impossible
imageSubstitution (a :: rest) sigma LHere = shadowTerm (sigma Here)
imageSubstitution (a :: rest) sigma (LThere v) = imageSubstitution rest (\x => sigma (There x)) v

public export
imageSubstitutionCorrect : (source : Vect n Ty) -> {0 target : Vect m Ty} ->
  (sigma : Substitution source target) -> SubstitutionImage sigma (imageSubstitution source sigma)
imageSubstitutionCorrect [] sigma v impossible
imageSubstitutionCorrect (a :: rest) sigma Here = Refl
imageSubstitutionCorrect (a :: rest) sigma (There v) = imageSubstitutionCorrect rest (\x => sigma (There x)) v

public export
shadowSubstitutionCommutes : (source : Vect n Ty) -> {0 target : Vect m Ty} ->
  (sigma : Substitution source target) -> (t : Term source a) ->
  shadowTerm (substitute sigma t) = substituteLogical (imageSubstitution source sigma) (shadowTerm t)
shadowSubstitutionCommutes source sigma t = shadowSubstitute sigma (imageSubstitution source sigma) (imageSubstitutionCorrect source sigma) t
