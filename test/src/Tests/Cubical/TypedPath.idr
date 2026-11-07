module Tests.Cubical.TypedPath

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Cubical.Logical.TypedPath
import Fibril.Foundation.DeMorgan.Face
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope


%default total

-- All derivations are checked by Idris; neither endpoints nor the path type
-- are trusted annotations. The context is one variable of A.
constant : HasType {m = 1} {n = 0} (Abstract (Variable FZ))
  (Path Universe (Variable FZ) (Variable FZ))
constant = PathIntro Base (BaseVar FZ) (BaseVar FZ) (BaseVar FZ) Refl Refl

application : HasType {m = 1} {n = 0} (Apply (Abstract (Variable FZ)) Zero) Universe
application = PathElim constant Zero

nested : HasType {m = 1} {n = 0} (Abstract (Abstract (Variable FZ)))
  (Path (Path Universe (Variable FZ) (Variable FZ))
    (Abstract (Variable FZ)) (Abstract (Variable FZ)))
nested = PathIntro (PathForm Base (BaseVar FZ) (BaseVar FZ)) constant constant
  (PathIntro Base (BaseVar FZ) (BaseVar FZ) (BaseVar FZ) Refl Refl) Refl Refl

-- The body really depends on the bound dimension. This judgment does not
-- identify the two applications by beta conversion.
varying : HasType {m = 1} {n = 0}
  (Abstract (Apply (Abstract (Variable FZ)) (Var FZ)))
  (Path Universe (Apply (Abstract (Variable FZ)) Zero)
                 (Apply (Abstract (Variable FZ)) One))
varying = PathIntro Base (PathElim constant Zero) (PathElim constant One)
  (PathElim (PathIntro Base (BaseVar FZ) (BaseVar FZ) (BaseVar FZ) Refl Refl) (Var FZ)) Refl Refl

-- A neutral path declaration refers only to base variables.
neutralContext : PathContext 2 1
neutralContext = [PathBetween FZ (FS FZ)]

neutralApplication : NeutralHasType Tests.Cubical.TypedPath.neutralContext STop
  (NApply (NPath FZ) (Var FZ)) NType
neutralApplication = NElim (NPathVar FZ) (Var FZ)

neutralLeftRestricted : NeutralEqual {n = 1} Tests.Cubical.TypedPath.neutralContext (SEndpoint FZ False)
  (NApply (NPath FZ) (Var FZ)) (NBase FZ) NType
neutralLeftRestricted = NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl

neutralMeetLeft : NeutralEqual {n = 2} Tests.Cubical.TypedPath.neutralContext (SEndpoint (FS FZ) False)
  (NApply (NPath FZ) (Meet (Var (FS FZ)) (Var FZ))) (NBase FZ) NType
neutralMeetLeft = NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl

nonBooleanFace : boundedFaceEntails {n = 1} STop
  (SDisjunction (SEndpoint FZ False) (SEndpoint FZ True)) = False
nonBooleanFace = Refl

-- Both endpoints vary with the bound dimension.
varyingFamily : NeutralTypeFormed {n = 1} Tests.Cubical.TypedPath.neutralContext STop
  (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
varyingFamily = NPathForm NBaseForm (NElim (NPathVar FZ) (Var FZ)) (NElim (NPathVar FZ) (Var FZ))

pathPForm : NeutralTypeFormed {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NPathType (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
    (NAbstract (NApply (NPath FZ) Zero))
    (NAbstract (NApply (NPath FZ) One)))
pathPForm = NPathPForm varyingFamily
  (NIntro NBaseForm (NElim (NPathVar FZ) Zero) (NElim (NPathVar FZ) Zero)
    (NElim (NPathVar FZ) Zero) (NRefl (NElim (NPathVar FZ) Zero)) (NRefl (NElim (NPathVar FZ) Zero)))
  (NIntro NBaseForm (NElim (NPathVar FZ) One) (NElim (NPathVar FZ) One)
    (NElim (NPathVar FZ) One) (NRefl (NElim (NPathVar FZ) One)) (NRefl (NElim (NPathVar FZ) One)))

pathPConstant : NeutralHasType {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NAbstract (NBase FZ)) (NPathType NType (NBase FZ) (NBase FZ))
pathPConstant = NPathPIntro NBaseForm (NBaseVar FZ) (NBaseVar FZ)
  (NBaseVar FZ) (NRefl (NBaseVar FZ)) (NRefl (NBaseVar FZ))

pathPApplication : NeutralHasType {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NApply (NAbstract (NBase FZ)) Zero) NType
pathPApplication = NPathPElim pathPConstant Zero

pathPLeft : NeutralEqual {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NApply (NAbstract (NBase FZ)) Zero) (NBase FZ) NType
pathPLeft = NPathPEndpointLeft pathPConstant (NBaseVar FZ) Refl

-- Elimination computes the family at the supplied interval, rather than
-- returning the uninstantiated family or a fixed carrier.
varyingElimination : NeutralHasType {n = 0} Tests.Cubical.TypedPath.neutralContext STop p
  (NPathType (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ))) l r) ->
  NeutralHasType Tests.Cubical.TypedPath.neutralContext STop (NApply p One)
    (NPathType NType (NApply (NPath FZ) One) (NApply (NPath FZ) One))
varyingElimination h = NPathPElim h One

pathPRight : NeutralEqual {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NApply (NAbstract (NBase FZ)) One) (NBase FZ) NType
pathPRight = NPathPEndpointRight pathPConstant (NBaseVar FZ) Refl

-- Substitution reaches the outer dimension beneath the abstraction, without
-- capturing or replacing its freshly bound dimension.
pathPSubstitutionShadowing :
  mapNeutralDimensions (instantiateDimension Zero)
    (NAbstract (NApply (NPath {m = 2} {k = 1} FZ)
      (Meet (Var FZ) (Var (FS FZ))))) =
  NAbstract (NApply (NPath FZ) (Meet (Var FZ) Zero))
pathPSubstitutionShadowing = Refl

-- Conditional on a path-over of the varying family: the endpoint is actually
-- derived at the family instantiated at Zero, rather than assumed at a carrier.
varyingEndpointAtZero :
  NeutralHasType {n = 0} Tests.Cubical.TypedPath.neutralContext STop p
    (NPathType
      (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
      (NAbstract (NApply (NPath FZ) Zero))
      (NAbstract (NApply (NPath FZ) One))) ->
  NeutralEqual Tests.Cubical.TypedPath.neutralContext STop
    (NApply p Zero) (NAbstract (NApply (NPath FZ) Zero))
    (NPathType NType (NApply (NPath FZ) Zero) (NApply (NPath FZ) Zero))
varyingEndpointAtZero h = NPathPEndpointLeft h
  (NIntro NBaseForm (NElim (NPathVar FZ) Zero) (NElim (NPathVar FZ) Zero)
    (NElim (NPathVar FZ) Zero) (NRefl (NElim (NPathVar FZ) Zero))
    (NRefl (NElim (NPathVar FZ) Zero))) Refl

-- The endpoint derivation itself is concrete at the open instantiated carrier.
-- The path-over remains a hypothetical judgment, since this slice cannot yet
-- construct the necessary varying-family boundary conversion.
varyingEndpointAtOpenZero :
  NeutralHasType {n = 1} Tests.Cubical.TypedPath.neutralContext (SEndpoint FZ False) p
    (NPathType
      (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
      (NAbstract (NApply (NPath FZ) (Var (FS FZ))))
      (NAbstract (NApply (NPath FZ) One))) ->
  NeutralEqual Tests.Cubical.TypedPath.neutralContext (SEndpoint FZ False)
    (NApply p (Var FZ)) (NAbstract (NApply (NPath FZ) (Var (FS FZ))))
    (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
varyingEndpointAtOpenZero h = NPathPEndpointLeft h
  (NIntro NBaseForm (NElim (NPathVar FZ) (Var FZ)) (NElim (NPathVar FZ) (Var FZ))
    (NElim (NPathVar FZ) (Var (FS FZ)))
    (NRefl (NElim (NPathVar FZ) (Var (FS FZ))))
    (NRefl (NElim (NPathVar FZ) (Var (FS FZ))))) Refl

-- Congruence is restricted to the very face on which the endpoint equality
-- was established; both source and target path types are formed there.
restrictedPathTypeCongruence :
  NeutralTypeEqual {n = 1} Tests.Cubical.TypedPath.neutralContext (SEndpoint FZ False)
    (NPathType NType (NApply (NPath FZ) (Var FZ)) (NApply (NPath FZ) (Var FZ)))
    (NPathType NType (NBase FZ) (NBase FZ))
restrictedPathTypeCongruence = NPathTypeCong NBaseForm
  (NElim (NPathVar FZ) (Var FZ)) (NElim (NPathVar FZ) (Var FZ))
  (NBaseVar FZ) (NBaseVar FZ) neutralLeftRestricted neutralLeftRestricted

restrictedConvertedPath :
  NeutralHasType {n = 1} Tests.Cubical.TypedPath.neutralContext (SEndpoint FZ False)
    (NAbstract (NApply (NPath FZ) (Var (FS FZ))))
    (NPathType NType (NBase FZ) (NBase FZ))
restrictedConvertedPath = NConvert
  (NIntro NBaseForm (NElim (NPathVar FZ) (Var FZ)) (NElim (NPathVar FZ) (Var FZ))
    (NElim (NPathVar FZ) (Var (FS FZ)))
    (NRefl (NElim (NPathVar FZ) (Var (FS FZ))))
    (NRefl (NElim (NPathVar FZ) (Var (FS FZ)))))
  restrictedPathTypeCongruence

-- The inner edge of the square, with the outer dimension still free.
squareInner : NeutralHasType {n = 1} Tests.Cubical.TypedPath.neutralContext STop
  (NAbstract (NApply (NPath FZ) (Meet (Var (FS FZ)) (Var FZ))))
  (NPathType NType (NBase FZ) (NApply (NPath FZ) (Var FZ)))
squareInner = NIntro NBaseForm (NBaseVar FZ) (NElim (NPathVar FZ) (Var FZ))
  (NElim (NPathVar FZ) (Meet (Var (FS FZ)) (Var FZ)))
  (NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl)
  (NIntervalApplyCong (NPathVar FZ) (IMeetRightOne Refl))

squareRightCong : NeutralEqual {n = 1} Tests.Cubical.TypedPath.neutralContext STop
  (NApply (NPath FZ) (Meet (Var FZ) One)) (NApply (NPath FZ) (Var FZ)) NType
squareRightCong = NIntervalApplyCong (NPathVar FZ) (IMeetRightOne Refl)

dependentAbstractRefl : NeutralEqual {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NAbstract (NBase FZ)) (NAbstract (NBase FZ))
  (NPathType NType (NBase FZ) (NBase FZ))
dependentAbstractRefl = NPathPAbstractCong pathPConstant pathPConstant (NRefl (NBaseVar FZ))
