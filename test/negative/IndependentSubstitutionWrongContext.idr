module IndependentSubstitutionWrongContext
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

sourceUses : Uses IndependentSubstitutionWrongContext.source [Linear]
sourceUses = UseIf (UseRef Here) UseBoolean UseBoolean

decls : PathDeclarations [LBool] [LBool]
decls = DeclarePath (shadowTerm IndependentSubstitutionWrongContext.source) (LBoolean False) NoPaths

path : DeclaredShadowPath IndependentSubstitutionWrongContext.decls (the (ScopedFace 0) STop)
  (Embed (shadowTerm IndependentSubstitutionWrongContext.source)) (Embed (LBoolean False))
path = ShadowAbstract (NeutralAt LHere (Var FZ))
  (BodyEndpoint (DeclaredLeft DeclaredHere Refl))
  (BodyEndpoint (DeclaredRight DeclaredHere Refl))

bad : CommonShadowPath
  (commonDeclarations (the (PathDeclarations [LUnit] [LBool]) (DeclarePath (LIf (LBoolean True) (LBoolean True) (LBoolean False)) (LBoolean False) NoPaths)))
  (the (ScopedFace 0) STop) (CPOrdinary (CIf (CBool True) (CBool True) (CBool False))) (CPOrdinary (CBool False)) LBool
bad = case commonQuantitativeIndependentPath [BoolTy] (SubstituteHere (Boolean True)) IndependentSubstitutionWrongContext.source [Linear] IndependentSubstitutionWrongContext.sourceUses [] (ReplacementHere UseBoolean) (commonDeclarations IndependentSubstitutionWrongContext.decls) (commonDeclaredShadowPath IndependentSubstitutionWrongContext.path) of
  (_, _, result) => result
