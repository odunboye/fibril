module Tests.Cubical.TypedPath

import Data.Fin
import Data.Vect
import Fibril.Cubical.Logical.PathContext
import Fibril.Cubical.Logical.OpenPath
import Fibril.Cubical.Logical.ScopedSyntax
import Fibril.Cubical.Logical.TypedPath
import Fibril.Cubical.Logical.TypedPathChecker

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

coincidentContext : PathContext 2 1
coincidentContext = [PathBetween FZ FZ]

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
-- This particular path-over remains a hypothetical judgment; the separate
-- square derivation below constructs a different varying family.
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

-- The actual square: the outer PathP family has right endpoint p i.
leftEdge : NeutralHasType {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NAbstract (NBase FZ)) (NPathType NType (NBase FZ) (NBase FZ))
leftEdge = NIntro NBaseForm (NBaseVar FZ) (NBaseVar FZ) (NBaseVar FZ)
  (NRefl (NBaseVar FZ)) (NRefl (NBaseVar FZ))

rightEdge : NeutralHasType {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NAbstract (NApply (NPath FZ) (Var FZ)))
  (NPathType NType (NBase FZ) (NBase (FS FZ)))
rightEdge = NIntro NBaseForm (NBaseVar FZ) (NBaseVar (FS FZ))
  (NElim (NPathVar FZ) (Var FZ))
  (NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl)
  (NEndpointRight (NPathVar FZ) (NBaseVar (FS FZ)) Refl)

square : NeutralHasType {n = 0} Tests.Cubical.TypedPath.neutralContext STop
  (NAbstract (NAbstract (NApply (NPath FZ) (Meet (Var (FS FZ)) (Var FZ)))))
  (NPathType (NPathType NType (NBase FZ) (NApply (NPath FZ) (Var FZ)))
    (NAbstract (NBase FZ)) (NAbstract (NApply (NPath FZ) (Var FZ))))
square = NPathPIntro
  (NPathForm NBaseForm (NBaseVar FZ) (NElim (NPathVar FZ) (Var FZ)))
  (NConvert leftEdge (NPathTypeCong NBaseForm (NBaseVar FZ) (NBaseVar FZ)
    (NBaseVar FZ) (NElim (NPathVar FZ) Zero) (NRefl (NBaseVar FZ))
    (NSym (NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl))))
  (NConvert rightEdge (NPathTypeCong NBaseForm (NBaseVar FZ) (NBaseVar (FS FZ))
    (NBaseVar FZ) (NElim (NPathVar FZ) One) (NRefl (NBaseVar FZ))
    (NSym (NEndpointRight (NPathVar FZ) (NBaseVar (FS FZ)) Refl))))
  squareInner
  (NAbstractCong {a = NType}
    (NFaceRestrict squareInner Refl)
    (NConvert
      (NIntro NBaseForm (NBaseVar FZ) (NBaseVar FZ) (NBaseVar FZ)
        (NRefl (NBaseVar FZ)) (NRefl (NBaseVar FZ)))
      (NPathTypeCong NBaseForm (NBaseVar FZ) (NBaseVar FZ)
        (NBaseVar FZ) (NElim (NPathVar FZ) (Var FZ))
        (NRefl (NBaseVar FZ))
        (NSym (NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl))))
    (NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl))
  (NAbstractCong {a = NType}
    (NFaceRestrict squareInner Refl)
    (NConvert
      (NIntro NBaseForm (NBaseVar FZ) (NBaseVar (FS FZ))
        (NElim (NPathVar FZ) (Var FZ))
        (NEndpointLeft (NPathVar FZ) (NBaseVar FZ) Refl)
        (NEndpointRight (NPathVar FZ) (NBaseVar (FS FZ)) Refl))
      (NPathTypeCong NBaseForm (NBaseVar FZ) (NBaseVar (FS FZ))
        (NBaseVar FZ) (NElim (NPathVar FZ) (Var FZ))
        (NRefl (NBaseVar FZ)) (NSym (NEndpointRight (NPathVar FZ) (NBaseVar (FS FZ)) Refl))))
    (NIntervalApplyCong (NPathVar FZ) (IMeetLeftOne Refl)))

convertedEquality : NeutralEqual {n = 1} Tests.Cubical.TypedPath.neutralContext (SEndpoint FZ False)
  (NAbstract (NApply (NPath FZ) (Var (FS FZ))))
  (NAbstract (NApply (NPath FZ) (Var (FS FZ))))
  (NPathType NType (NBase FZ) (NBase FZ))
convertedEquality = NEqualConvert
  (NRefl (NIntro NBaseForm (NElim (NPathVar FZ) (Var FZ)) (NElim (NPathVar FZ) (Var FZ))
    (NElim (NPathVar FZ) (Var (FS FZ)))
    (NRefl (NElim (NPathVar FZ) (Var (FS FZ))))
    (NRefl (NElim (NPathVar FZ) (Var (FS FZ))))))
  restrictedPathTypeCongruence restrictedConvertedPath restrictedConvertedPath

checkerSuccess : Either CheckError a -> Bool
checkerSuccess (Right _) = True
checkerSuccess _ = False

checkerMismatch : Either CheckError a -> Bool
checkerMismatch (Left Mismatch) = True
checkerMismatch _ = False

checkerExhausted : Either CheckError a -> Bool
checkerExhausted (Left Exhausted) = True
checkerExhausted _ = False

checkerUnsupported : Either CheckError a -> Bool
checkerUnsupported (Left Unsupported) = True
checkerUnsupported _ = False

public export
checkerChecks : List (String, Bool)
checkerChecks =
  [ ("checker connection inner edge", checkerSuccess (checkNeutral {n = 1} 64 neutralContext STop
      (NAbstract (NApply (NPath FZ) (Meet (Var (FS FZ)) (Var FZ))))
      (NPathType NType (NBase FZ) (NApply (NPath FZ) (Var FZ)))))
  , ("checker connection wrong endpoint", checkerMismatch (checkNeutral {n = 1} 64 neutralContext STop
      (NAbstract (NApply (NPath FZ) (Meet (Var (FS FZ)) (Var FZ))))
      (NPathType NType (NBase (FS FZ)) (NApply (NPath FZ) (Var FZ)))))
  , ("checker meet congruence", checkerSuccess (checkNeutralEqual {n = 1} 64 neutralContext STop
      (NApply (NPath FZ) (Meet (Var FZ) One)) (NApply (NPath FZ) (Var FZ))))
  , ("checker face escape rejected", checkerUnsupported (checkNeutralEqual {n = 2} 64 neutralContext STop
      (NApply (NPath FZ) (Meet (Var FZ) (Var (FS FZ)))) (NApply (NPath FZ) (Var FZ))))
  , ("checker non-boolean meet rejected", checkerUnsupported (checkNeutralEqual {n = 1} 64 neutralContext STop
      (NApply (NPath FZ) (Meet (Var FZ) (Reverse (Var FZ)))) (NBase FZ)))
  , ("checker endpoint conversion", checkerSuccess (checkNeutralEqual {n = 1} 64 neutralContext (SEndpoint FZ False)
      (NApply (NPath FZ) (Var FZ)) (NBase FZ)))
  , ("checker coincident endpoint zero", checkerSuccess (checkNeutralEqual {n = 0} 32 coincidentContext STop
      (NApply (NPath FZ) Zero) (NBase FZ)))
  , ("checker coincident endpoint one", checkerSuccess (checkNeutralEqual {n = 0} 32 coincidentContext STop
      (NApply (NPath FZ) One) (NBase FZ)))
  , ("checker coincident disjunctive right goal", checkerSuccess (checkNeutralEqual {n = 2} 64 coincidentContext (SEndpoint FZ True)
      (NApply (NPath FZ) (Join (Var FZ) (Var (FS FZ)))) (NBase FZ)))
  , ("checker disjunctive face not entailed", checkerUnsupported (checkNeutralEqual {n = 1} 64 coincidentContext
      (SDisjunction (SEndpoint FZ False) (SEndpoint FZ True))
      (NApply (NPath FZ) (Var FZ)) (NBase FZ)))
  , ("checker coincident endpoint wrong target", checkerMismatch (checkNeutralEqual {n = 0} 32 coincidentContext STop
      (NApply (NPath FZ) One) (NBase (FS FZ))))
  , ("checker matching left without entailment", checkerUnsupported (checkNeutralEqual {n = 0} 32 neutralContext STop
      (NApply (NPath FZ) One) (NBase FZ)))
  , ("checker coincident endpoint exhausted", checkerExhausted (checkNeutralEqual {n = 0} 1 coincidentContext STop
      (NApply (NPath FZ) One) (NBase FZ)))
  , ("checker equality exhausted", checkerExhausted (checkNeutralEqual {n = 1} 2 neutralContext STop
      (NApply (NPath FZ) (Meet (Var FZ) One)) (NApply (NPath FZ) (Var FZ))))
  , ("checker open abstraction", checkerSuccess (checkNeutral {n = 0} 32 neutralContext STop
      (NAbstract (NApply (NPath FZ) (Var FZ)))
      (NPathType NType (NBase FZ) (NBase (FS FZ)))))
  , ("checker false face", checkerSuccess (checkNeutral {n = 1} 32 neutralContext SBottom
      (NApply (NPath FZ) (Var FZ)) NType))
  , ("checker annotation mismatch", checkerMismatch (checkNeutral {n = 0} 32 neutralContext STop
      (NPath FZ) (NPathType NType (NBase (FS FZ)) (NBase FZ))))
  , ("checker exhausted", checkerExhausted (checkNeutral {n = 1} 2 neutralContext STop
      (NApply (NPath FZ) (Var FZ)) NType))
  , ("checker unsupported", checkerUnsupported (checkNeutral {n = 0} 32 neutralContext STop
      (NAbstract (NAbstract (NBase FZ))) NType))
  , ("checker entailment limit fails closed", checkerUnsupported (checkNeutral {n = 12} 32 neutralContext STop
      (NAbstract (NApply (NPath FZ) (Var FZ)))
      (NPathType NType (NBase FZ) (NBase (FS FZ)))))
  , ("checker good annotation", checkerSuccess (checkNeutral {n = 0} 32 neutralContext STop
      (NPath FZ) (NPathType NType (NBase FZ) (NBase (FS FZ)))))
  , ("checker formation", checkerSuccess (checkNeutralFormation {n = 0} 32 neutralContext STop
      (NPathType NType (NApply (NPath FZ) Zero) (NBase FZ))))
  ]
