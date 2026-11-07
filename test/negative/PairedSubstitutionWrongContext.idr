module PairedSubstitutionWrongContext
import Data.Vect
import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Usage
import Fibril.Core.Quantitative.Syntax
import Fibril.Core.Quantitative.Substitution
import Fibril.Core.Quantitative.Usage
import Fibril.Cubical.Logical.Shadow
import Fibril.Cubical.Logical.ShadowPath
import Fibril.Cubical.Logical.ShadowTypedBridge
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Foundation.DeMorgan.Face
import Fibril.Cubical.Logical.ShadowCommon
import Fibril.Cubical.Logical.ShadowSubstitution
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

source : Term [BoolTy] BoolTy
source = If (Ref Here) (Boolean True) (Boolean False)

sourceUses : Uses PairedSubstitutionWrongContext.source [Linear]
sourceUses = UseIf (UseRef Here) UseBoolean UseBoolean

decls : PathDeclarations [LBool] [LBool]
decls = DeclarePath (shadowTerm PairedSubstitutionWrongContext.source) (LBoolean False) NoPaths

path : DeclaredShadowPath PairedSubstitutionWrongContext.decls (the (ScopedFace 0) STop)
  (Embed (shadowTerm PairedSubstitutionWrongContext.source)) (Embed (LBoolean False))
path = ShadowAbstract (NeutralAt LHere (Var FZ))
  (BodyEndpoint (DeclaredLeft DeclaredHere Refl))
  (BodyEndpoint (DeclaredRight DeclaredHere Refl))

bad : CommonShadowPath
  (commonDeclarations (the (PathDeclarations [LUnit] [LBool]) (DeclarePath (LIf (LBoolean True) (LBoolean True) (LBoolean False)) (LBoolean False) NoPaths)))
  (the (ScopedFace 0) STop) (CPOrdinary (CIf (CBool True) (CBool True) (CBool False))) (CPOrdinary (CBool False)) LBool
bad = case commonQuantitativeSubstitution [BoolTy] (SubstituteHere (Boolean True)) PairedSubstitutionWrongContext.source [Linear] PairedSubstitutionWrongContext.sourceUses [] (ReplacementHere UseBoolean) PairedSubstitutionWrongContext.path of
  (_, _, result) => result
